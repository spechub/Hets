{- |
Module      :  $Header$
Copyright   :  Eugen Kuksa 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

Analyses CommonLogic files.
-}

module CommonLogic.ParseCLAsLibDefn (parseCL_CLIF) where

import Common.Id
import Common.LibName
import Common.AS_Annotation as Anno
import Common.AnnoState

import Driver.Options

import Text.ParserCombinators.Parsec

import Logic.Grothendieck

import CommonLogic.AS_CommonLogic as CL
import CommonLogic.Logic_CommonLogic
import CommonLogic.Parse_CLIF (basicSpec)

import Syntax.AS_Library
import Syntax.AS_Structured as Struc

import Control.Monad (foldM)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (elemIndex, sortBy)

import System.IO
import System.FilePath (combine, addExtension)
import System.Directory (doesFileExist, getCurrentDirectory)


--                 specName  (spec, topTexts)
type SpecMap = Map String (BASIC_SPEC, Set String)

-- | call for CommonLogic CLIF-parser with recursive inclusion of importations
parseCL_CLIF :: FilePath -> HetcatsOpts -> IO LIB_DEFN
parseCL_CLIF filename opts = do
  maybeText <- parseCL_CLIF_file filename
  case maybeText of
      Right bs ->
        let fn = convertFileToLibStr filename
            ns = specNameL bs fn
            specMap = foldr (\(b,n) r -> Map.insertWith unify n (b, Set.empty) r) Map.empty (zip bs ns)
        in do
            specs <- anaImports opts specMap
            return $ convertToLibDefN fn specs
      Left x -> error $ show x

-- call for CommonLogic CLIF-parser for a single file
parseCL_CLIF_file :: FilePath -> IO (Either ParseError [BASIC_SPEC])
parseCL_CLIF_file filename = do
  handle <- openFile filename ReadMode
  contents <- hGetContents handle
  return $ runParser (many basicSpec) (emptyAnnos ())
                       ("Error parsing CLIF-File \"" ++ filename++"\"") contents

-- maps imports in basic spec to global definition links (extensions) in
-- development graph
convertToLibDefN :: String -> [(BASIC_SPEC, NAME)] -> LIB_DEFN
convertToLibDefN fn specs =
  Lib_defn
    (emptyLibName fn)
    (emptyAnno (Logic_decl (Logic_name
                              (mkSimpleId $ show CommonLogic)
                              Nothing
                              Nothing
                          ) nullRange)
      : (map convertToLibItems specs
        ++ concatMap convertMetarelsToLibItems specs)
    )
    nullRange
    []

convertToLibItems :: (BASIC_SPEC, NAME) -> Anno.Annoted LIB_ITEM
convertToLibItems (b,n) =
  emptyAnno $ Spec_defn n emptyGenericity (createSpec b) nullRange

createSpec :: BASIC_SPEC -> Anno.Annoted SPEC
createSpec b =
  let imports = Set.elems $ directImports b
      bs = emptyAnno $ Struc.Basic_spec (G_basic_spec CommonLogic b) nullRange
  in  case imports of
          [] -> bs
          _  -> emptyAnno $ Extension [
              (case imports of
                   [n] -> specFromName n
                   _   -> emptyAnno $ Union (map specFromName imports) nullRange)
              , bs
            ] nullRange

specFromName :: NAME -> Annoted SPEC
specFromName n = emptyAnno $ Spec_inst n [] nullRange

specNameL :: [BASIC_SPEC] -> String -> [String]
specNameL bs def = map (\(i,b) -> specName i b def) $ zip [0..] bs

-- returns a unique name for a node
specName :: Int -> CL.BASIC_SPEC -> String -> String
specName i (CL.Basic_spec []) def = def ++ "_" ++ show i
specName i (CL.Basic_spec [items]) def =
  case Anno.item items of
       Axiom_items ax ->
          case getText $ Anno.item ax of
               Text _ _ -> def ++ "_" ++ show i
               Named_text n _ _ -> n
specName i (CL.Basic_spec (_:_)) def = def ++ "_" ++ show i

convertMetarelsToLibItems :: (BASIC_SPEC, NAME) -> [Anno.Annoted LIB_ITEM]
convertMetarelsToLibItems (CL.Basic_spec abis, n) =
  concatMap (metarelsBI n . Anno.item) abis

metarelsBI :: NAME -> BASIC_ITEMS -> [Anno.Annoted LIB_ITEM]
metarelsBI n (Axiom_items (Anno.Annoted tm _ _ _)) =
  concatMap (metarelsMR n) $ Set.elems $ metarelation tm

metarelsMR :: NAME -> METARELATION -> [Anno.Annoted LIB_ITEM]
metarelsMR n mr = case mr of
  RelativeInterprets delta t2 smaps ->
      [emptyAnno $ View_defn
                          (mkSimpleId $ concat [ "RelativeInterprets_"
                                               , show n, "_"
                                               , show delta, "_"
                                               , show t2 ])
                          emptyGenericity
                          (View_type
                            (specFromName t2)
                            (emptyAnno (Union [specFromName n, specFromName delta] nullRange))
                            nullRange)
                          [G_symb_map $ G_symb_map_items_list CommonLogic smaps]
                          nullRange]
  NonconservativeExtends t2 smaps ->
      [emptyAnno $ View_defn
                          (mkSimpleId $ concat [ "NonconservativeExtends_"
                                               , show n, "_"
                                               , show t2 ])
                          emptyGenericity
                          (View_type
                            (specFromName t2)
                            (specFromName n)
                            nullRange)
                          [G_symb_map $ G_symb_map_items_list CommonLogic smaps]
                          nullRange]
  IncludeLibs _ -> []
-- TODO: implement this for the other metarelations

collectDownloads :: HetcatsOpts -> SpecMap -> (String, (BASIC_SPEC, Set String))
                    -> IO SpecMap
collectDownloads opts specMap (n,(b,topTexts)) =
  let directDls = Set.elems $ Set.map tokStr $ directDownloads b
      newTopTexts = Set.insert n topTexts
  in  foldM (\sm d -> do
          newDls <- downloadSpec opts sm newTopTexts d
          return (Map.unionWith unify newDls sm)
        ) specMap directDls

downloadSpec :: HetcatsOpts -> SpecMap -> Set String -> String -> IO SpecMap
downloadSpec opts specMap topTexts n =
  case Map.lookup n specMap of
      Just (b, t) ->
          if  t == topTexts then return specMap else do
          let newTopTexts = Set.union t topTexts
          let newSpecMap = Map.insert n (b,newTopTexts) specMap
          collectDownloads opts newSpecMap (n,(b,newTopTexts))
      Nothing -> do
          curDir <- getCurrentDirectory
          file <- findLibFile (curDir:libdirs opts) n
          maybeText <- parseCL_CLIF_file file
          case maybeText of
              Left err -> error $ show err
              Right bs ->
                let ns = specNameL bs n
                    j = case elemIndex n ns of
                              Just i -> i
                              Nothing -> error $ "CL-Text not found: " ++ show n
                    b = bs !! j
                    nbt = (n, (b, topTexts))
                    newSpecMap = Map.insertWith unify n (b,topTexts) specMap
                in  collectDownloads opts newSpecMap nbt

unify :: (a, Set String) -> (a, Set String) -> (a, Set String)
unify (_, s) (a, t) = (a, Set.union s t)

-- yields the path to a CommonLogic-file with name @f@ (before the extension)
findLibFile :: [FilePath] -> String -> IO FilePath
findLibFile [] f = error $ "Could not find Common Logic Library " ++ f
findLibFile (d:ds) f =
  let f1 = (combine d (addExtension f (show CommonLogic2In)))
      f2 = (combine d (addExtension f (show CommonLogicIn)))
  in do
      f1Exists <- doesFileExist f1
      f2Exists <- doesFileExist f2
      case f1Exists of
        True -> return f1
        _ ->  case f2Exists of
                True -> return f2
                _ -> findLibFile ds f

directDownloads :: BASIC_SPEC -> Set NAME
directDownloads b = Set.union (directMetarels b) (directImports b)

-- retrieves all importations from the text
directImports :: BASIC_SPEC -> Set NAME
directImports (CL.Basic_spec items) =
  Set.unions $ map (getImports_textMeta . textFromBasicItems . Anno.item) items

textFromBasicItems :: BASIC_ITEMS -> TEXT_META
textFromBasicItems (Axiom_items annoText) = Anno.item annoText

getImports_textMeta :: TEXT_META -> Set NAME
getImports_textMeta tm = getImports_text $ getText tm

getImports_text :: TEXT -> Set NAME
getImports_text (Named_text _ t _) = getImports_text t
getImports_text (Text p _) = Set.fromList $ map impName $ filter isImportation p

isImportation :: PHRASE -> Bool
isImportation (Importation _) = True
isImportation _ = False

impName :: PHRASE -> NAME
impName (Importation (Imp_name n)) = n
impName _ = undefined -- not necessary because filtered out

directMetarels :: BASIC_SPEC -> Set NAME
directMetarels (CL.Basic_spec abis) =
  Set.unions $ map (metarelDownloadsBI . Anno.item) abis

metarelDownloadsBI :: BASIC_ITEMS -> Set NAME
metarelDownloadsBI (Axiom_items (Anno.Annoted tm _ _ _)) =
  Set.fold Set.union Set.empty $ Set.map metarelDownloadsMR $ metarelation tm

metarelDownloadsMR :: METARELATION -> Set NAME
metarelDownloadsMR mr = case mr of
  RelativeInterprets delta t2 _ -> Set.fromList [delta, t2]
  NonconservativeExtends t2 _ -> Set.singleton  t2
  IncludeLibs ns -> Set.fromList ns
-- TODO: implement this for the other metarelations

anaImports :: HetcatsOpts -> SpecMap -> IO [(BASIC_SPEC, NAME)]
anaImports opts specMap = do
  downloads <- foldM
    (\sm nbt -> do
      newSpecs <- collectDownloads opts sm nbt
      return (Map.unionWith unify newSpecs sm)
    ) specMap $ Map.assocs specMap
  let specAssocs = Map.assocs $ Map.unionWith unify specMap downloads
  let sortedSpecs = sortBy usingTopTextsCount specAssocs -- sort by putting the latest imported specs to the beginning
  return $ bsNamePairs sortedSpecs

-- not fast (O(n+m)), but reliable
usingTopTextsCount :: (t, (a, Set t)) -> (t, (b, Set t)) -> Ordering
usingTopTextsCount (_,(_,topTexts1)) (_,(_,topTexts2)) =
  compare (Set.size topTexts2) (Set.size topTexts1)

{- 
-- not an elegant way, but seems to work
hierarchical ::Ord t => (t, (a, Set t)) -> (t, (b, Set t)) -> Ordering
hierarchical (n1, (_, topTexts1)) (n2, (_, topTexts2)) =
  if Set.null topTexts1 then GT else
  if Set.null topTexts2 then LT else 
  if Set.member n1 topTexts2 && Set.member n2 topTexts1 then EQ else
  if Set.member n1 topTexts2 then GT else
  if Set.member n2 topTexts1 then LT else
  if Set.isSubsetOf topTexts1 topTexts2 then LT else
  if Set.isSubsetOf topTexts2 topTexts1 then GT else
  if Set.null $ Set.intersection topTexts1 topTexts2 then EQ else EQ
-}

bsNamePairs :: [(String, (BASIC_SPEC, Set String))] -> [(BASIC_SPEC, NAME)]
bsNamePairs = foldr (\(n,(b,_)) r -> (b, mkSimpleId n) : r) []
