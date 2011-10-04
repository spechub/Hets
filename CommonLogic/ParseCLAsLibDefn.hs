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

import qualified Data.Set as Set

import System.IO
import System.FilePath (combine, addExtension)
import System.Directory (doesFileExist, getCurrentDirectory)

-- | call for CommonLogic CLIF-parser
parseCL_CLIF :: FilePath -> HetcatsOpts -> IO LIB_DEFN
parseCL_CLIF filename opts = do
  maybeText <- parseCL_CLIF_file filename
  case maybeText of
      Right bs -> convertToLibDefN opts filename bs
      Left x -> error $ show x

parseCL_CLIF_file :: FilePath -> IO (Either ParseError [BASIC_SPEC])
parseCL_CLIF_file filename = do
  handle <- openFile filename ReadMode
  contents <- hGetContents handle
  return $ runParser (many basicSpec) (emptyAnnos ())
                               ("Error parsing CLIF-File " ++ filename) contents

-- maps imports in basic spec to global definition links (extensions) in
-- development graph
convertToLibDefN :: HetcatsOpts -> FilePath -> [BASIC_SPEC] -> IO LIB_DEFN
convertToLibDefN opts filename bs =
  let fn = convertFileToLibStr filename
      knownSpecs = map (\(i,b) -> specName i b fn) $ zip [0..] bs
  in do libItems <- convertToLibItems opts knownSpecs bs
        return $ Lib_defn
          (emptyLibName fn)
          (emptyAnno (Logic_decl (Logic_name
                                    (mkSimpleId $ show CommonLogic)
                                    Nothing
                                    Nothing
                                ) nullRange)
            : libItems
          )
          nullRange
          []

convertToLibItems :: HetcatsOpts -> [NAME] -> [BASIC_SPEC] -> IO [Anno.Annoted LIB_ITEM]
convertToLibItems opts knownSpecs bs =
  concatMapM (convertBS opts knownSpecs) $ zip bs knownSpecs

-- Creates Nodes in the Logic Graph.
-- Also gives each non-named text a unique name in the graph.
convertBS :: HetcatsOpts -> [NAME] -> (BASIC_SPEC, NAME) -> IO [Anno.Annoted LIB_ITEM]
convertBS opts knownSpecs (b,n) =
  let imports = getImports b
  in do
    downloads <- concatMapM (downloadIfNotKnown opts knownSpecs) imports
    metaRelations <- metarelsBS opts (knownSpecs++imports) b
    return $ downloads                     -- external imports
             ++ [emptyAnno $ Spec_defn     -- imports from known files
                 n
                 emptyGenericity
                 (createSpec imports b)
                 nullRange]
             ++ metaRelations              -- metarelations for colore

-- one importation is an extension
-- many importations are an extension of a union
createSpec :: [NAME] -> BASIC_SPEC -> Anno.Annoted SPEC
createSpec imports b =
  let bs = emptyAnno $ Struc.Basic_spec (G_basic_spec CommonLogic b) nullRange
  in  case imports of
          [] -> bs
          _  -> emptyAnno $ Extension [
              (case imports of
                   [n] -> cnvimport n
                   _   -> emptyAnno $ Union (map cnvimport imports) nullRange)
              , bs
            ] nullRange

-- converts an imporation name to a SPEC
cnvimport :: NAME -> Annoted SPEC
cnvimport n = emptyAnno $ Spec_inst n [] nullRange

-- retrieves all importations from the text
getImports :: BASIC_SPEC -> [NAME]
getImports (CL.Basic_spec items) =
  concatMap getImports_textMrs $ map textFromBasicItems items

textFromBasicItems :: Anno.Annoted (BASIC_ITEMS) -> TEXT_META
textFromBasicItems abi = case Anno.item abi of
                              Axiom_items annoText -> Anno.item annoText

getImports_textMrs :: TEXT_META -> [NAME]
getImports_textMrs tm = getImports_text $ getText tm

getImports_text :: TEXT -> [NAME]
getImports_text (Text ps _) = map impToName $ filter isImportation ps
getImports_text (Named_text _ t _) = getImports_text t

isImportation :: PHRASE -> Bool
isImportation (Importation _) = True
isImportation _ = False

impToName :: PHRASE -> NAME
impToName (Importation (Imp_name n)) = n
impToName _ = undefined -- not necessary because filtered out

-- returns a unique name for a node
specName :: Int -> CL.BASIC_SPEC -> String -> NAME
specName i (CL.Basic_spec []) def = mkSimpleId $ def ++ "_" ++ show i
specName i (CL.Basic_spec [items]) def =
  case Anno.item items of
       Axiom_items ax ->
          case getText $ Anno.item ax of
               Text _ _ -> mkSimpleId $ def ++ "_" ++ show i
               Named_text n _ _ -> mkSimpleId n
specName i (CL.Basic_spec (_:_)) def = mkSimpleId $ def ++ "_" ++ show i

metarelsBS :: HetcatsOpts -> [NAME] -> BASIC_SPEC -> IO [Anno.Annoted LIB_ITEM]
metarelsBS opts knownSpecs (CL.Basic_spec abis) =
  concatMapM (metarelsBI opts knownSpecs . Anno.item) abis

metarelsBI :: HetcatsOpts -> [NAME] -> BASIC_ITEMS -> IO [Anno.Annoted LIB_ITEM]
metarelsBI opts knownSpecs (Axiom_items (Anno.Annoted tm _ _ _)) =
  concatMapM (metarelsMR opts knownSpecs) $ Set.elems $ metarelation tm

metarelsMR :: HetcatsOpts -> [NAME] -> METARELATION -> IO [Anno.Annoted LIB_ITEM]
metarelsMR opts knownSpecs mr = case mr of
  RelativeInterprets t1 delta t2 smaps -> do
      downloads <- concatMapM (downloadIfNotKnown opts knownSpecs) [t1,delta,t2]
      return $ downloads
          ++ [emptyAnno $ View_defn
                          (mkSimpleId $ concat [ "RelativeInterprets "
                                               , show t1, " "
                                               , show delta, " "
                                               , show t2 ])
                          emptyGenericity
                          (View_type
                            (cnvimport t2)
                            (emptyAnno (Union [cnvimport t1, cnvimport delta] nullRange))
                            nullRange)
                          [G_symb_map $ G_symb_map_items_list CommonLogic smaps]
                          nullRange]
  NonconservativeExtends t1 t2 smaps -> do
      downloads <- concatMapM (downloadIfNotKnown opts knownSpecs) [t1,t2]
      return $ downloads
          ++ [emptyAnno $ View_defn
                          (mkSimpleId $ concat [ "NonconservativeExtends "
                                               , show t1, " "
                                               , show t2 ])
                          emptyGenericity
                          (View_type
                            (cnvimport t2)
                            (cnvimport t1)
                            nullRange)
                          [G_symb_map $ G_symb_map_items_list CommonLogic smaps]
                          nullRange]

downloadIfNotKnown :: HetcatsOpts -> [NAME] -> NAME -> IO [Anno.Annoted LIB_ITEM]
downloadIfNotKnown opts knownSpecs n =
  if elem n knownSpecs
  then return []
  else do
         curDir <- getCurrentDirectory
         file <- findLibFile (curDir:libdirs opts) (tokStr n)
         maybeText <- parseCL_CLIF_file file
         case maybeText of
              Right bs -> convertToLibItems opts (n:knownSpecs) bs
              Left err -> error $ show err

findLibFile :: [FilePath] -> String -> IO FilePath
findLibFile [] f = error $ "Could not find Library " ++ f
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

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = do
  ys <- mapM f xs
  return $ concat ys
