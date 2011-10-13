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
import Common.DocUtils

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
import Data.List (sortBy)

import System.IO
import System.FilePath (combine, addExtension)
import System.Directory (doesFileExist, getCurrentDirectory)

import Network.URI
import Network.HTTP


type SpecMap = Map String SpecInfo
type SpecInfo = (BASIC_SPEC, Set String, Set String)
                -- (spec, topTexts, importedBy)

-- | call for CommonLogic CLIF-parser with recursive inclusion of importations
parseCL_CLIF :: FilePath -> HetcatsOpts -> IO LIB_DEFN
parseCL_CLIF filename opts = do
  specMap <- downloadSpec opts Map.empty Set.empty Set.empty False filename
  specs <- anaImports opts specMap
  return $ convertToLibDefN (convertFileToLibStr filename) specs


-- call for CommonLogic CLIF-parser for a single file
parseCL_CLIF_contents :: FilePath -> String -> Either ParseError [BASIC_SPEC]
parseCL_CLIF_contents filename contents =
  runParser (many basicSpec) (emptyAnnos ())
                       ("Error while parsing CLIF-File \"" ++ filename++"\"") contents

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
specFromName n = emptyAnno $ Spec_inst (cnvImportName n) [] nullRange

specNameL :: [BASIC_SPEC] -> String -> [String]
specNameL [_] def = [def]
specNameL bs def = map (specName def) [0..(length bs)]

-- returns a unique name for a node
specName :: String -> Int -> String
specName def i = def ++ "_" ++ show i

cnvImportName :: NAME -> NAME
cnvImportName = mkSimpleId . convertFileToLibStr . tokStr

convertMetarelsToLibItems :: (BASIC_SPEC, NAME) -> [Anno.Annoted LIB_ITEM]
convertMetarelsToLibItems (CL.Basic_spec abis, n) =
  concatMap (metarelsBI n . Anno.item) abis

metarelsBI :: NAME -> BASIC_ITEMS -> [Anno.Annoted LIB_ITEM]
metarelsBI n (Axiom_items axs) = concatMap (metarelsTM n) axs

metarelsTM :: NAME -> Anno.Annoted TEXT_META -> [Anno.Annoted LIB_ITEM]
metarelsTM n annoTm =
  concatMap (metarelsMR n) $ Set.elems $ metarelation $ Anno.item annoTm

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

collectDownloads :: HetcatsOpts -> SpecMap -> (String, SpecInfo) -> IO SpecMap
collectDownloads opts specMap (n,(b,topTexts,importedBy)) =
  let -- directDls = Set.elems $ Set.map tokStr $ directDownloads b
      directMrs = Set.elems $ Set.map tokStr $ directMetarels b
      directImps = Set.elems $ Set.map tokStr $ directImports b
      newTopTexts = Set.insert n topTexts
      newImportedBy = Set.insert n importedBy
  in do
      sm2 <- foldM (\sm d -> do
          newDls <- downloadSpec opts sm newTopTexts newImportedBy True d
          return (Map.unionWith unify newDls sm)
        ) specMap directImps -- imports get @n@ as new "importedBy"
      foldM (\sm d -> do
          newDls <- downloadSpec opts sm newTopTexts Set.empty False d
          return (Map.unionWith unify newDls sm)
        ) sm2 directMrs -- metarelations have no "importedBy"s

downloadSpec :: HetcatsOpts -> SpecMap -> Set String -> Set String
                -> Bool -> String -> IO SpecMap
downloadSpec opts specMap topTexts importedBy isImport filename =
  let fn = convertFileToLibStr filename in
  case Map.lookup fn specMap of
      Just (b, t, i) ->
          if  isImport && Set.member (convertFileToLibStr filename) importedBy
          then error (concat [
                    "Illegal cyclic import: ", show (pretty importedBy), "\n"
                  , "Hets currently cannot handle cyclic imports "
                  , "of Common Logic files. "
                  , "If you really need them, send us a message at "
                  , "hets@informatik.uni-bremen.de, and we will fix it."
                ])
          else 
          if  t == topTexts then return specMap else do
          let newTopTexts = Set.union t topTexts
          let newImportedBy = Set.union i importedBy
          let newSpecMap = Map.insert fn (b,newTopTexts,newImportedBy) specMap
          collectDownloads opts newSpecMap (fn,(b,newTopTexts,newImportedBy))
      Nothing -> do
          contents <- getCLIFContents opts filename
          case parseCL_CLIF_contents filename contents of
              Left err -> error $ show err
              Right bs ->
                let nbs = zip (specNameL bs fn) bs
                    nbtis = map (\(n,b) -> (n, (b, topTexts,importedBy))) nbs
                    newSpecMap = foldr (\(n, bti) sm ->
                        Map.insertWith unify n bti sm
                      ) specMap nbtis
                in  foldM (\sm nbt -> do
                          newDls <- collectDownloads opts sm nbt
                          return (Map.unionWith unify newDls sm)
                      )  newSpecMap nbtis

unify :: SpecInfo -> SpecInfo -> SpecInfo
unify (_, s, p) (a, t, q) = (a, Set.union s t, Set.union p q)

--one could add support for uri fragments/query (perhaps select a text from the file)
getCLIFContents :: HetcatsOpts -> String -> IO String
getCLIFContents opts filename = case parseURIReference filename of
  Nothing -> do
    putStrLn ("Not an URI: " ++ filename)
    localFileContents opts filename
  Just uri -> do
    case uriScheme uri of
      "" -> do
        localFileContents opts ((uriToString id $ uri) "")
      "file:" -> do
        localFileContents opts (uriPath uri)
      "http:" -> do
        simpleHTTP (defaultGETRequest uri) >>= getResponseBody
      "https:" -> do
        simpleHTTP (defaultGETRequest uri) >>= getResponseBody
      x -> error ("Unsupported URI scheme: " ++ x)

localFileContents :: HetcatsOpts -> String -> IO String
localFileContents opts filename = do
  curDir <- getCurrentDirectory
  file <- findLibFile (curDir:libdirs opts) filename
  handle <- openFile file ReadMode
  hGetContents handle

findLibFile :: [FilePath] -> String -> IO FilePath
findLibFile [] f = error $ "Could not find Common Logic Library " ++ f
findLibFile (d:ds) f =
  let f0 = f
      f1 = (combine d (addExtension f (show CommonLogic2In)))
      f2 = (combine d (addExtension f (show CommonLogicIn)))
  in do
      f0Exists <- doesFileExist f0
      f1Exists <- doesFileExist f1
      f2Exists <- doesFileExist f2
      case f0Exists of
        True -> return f0
        _ -> case f1Exists of
                True -> return f1
                _ -> case f2Exists of
                        True -> return f2
                        _ -> findLibFile ds f

-- retrieves all importations from the text
directImports :: BASIC_SPEC -> Set NAME
directImports (CL.Basic_spec items) =
  Set.unions $ map (getImports_textMetas . textsFromBasicItems . Anno.item) items

textsFromBasicItems :: BASIC_ITEMS -> [TEXT_META]
textsFromBasicItems (Axiom_items axs) = map Anno.item axs

getImports_textMetas :: [TEXT_META] -> Set NAME
getImports_textMetas tms = Set.unions $ map (getImports_text . getText) tms

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
metarelDownloadsBI (Axiom_items axs) =
  Set.unions $ map (metarelDownloadsTM . Anno.item) axs

metarelDownloadsTM :: TEXT_META -> Set NAME
metarelDownloadsTM tm =
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
  let specAssocs = Map.assocs downloads
  let sortedSpecs = sortBy usingImportedByCount specAssocs -- sort by putting the latest imported specs to the beginning
  return $ bsNamePairs sortedSpecs

-- not fast (O(n+m)), but almost reliable (not working when mixing imports and metarelations)
usingImportedByCount :: (String, SpecInfo) -> (String, SpecInfo) -> Ordering
usingImportedByCount (_,(_,_,importedBy1)) (_,(_,_,importedBy2)) =
  compare (Set.size importedBy2) (Set.size importedBy1)

bsNamePairs :: [(String, SpecInfo)] -> [(BASIC_SPEC, NAME)]
bsNamePairs = foldr (\(n,(b,_,_)) r -> (b, mkSimpleId n) : r) []
