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
import Common.IRI
import Common.LibName
import Common.AS_Annotation as Anno
import Common.AnnoState
import Common.DocUtils

import Driver.Options

import Text.ParserCombinators.Parsec

import Logic.Grothendieck

import CommonLogic.AS_CommonLogic as CL
import CommonLogic.Logic_CommonLogic
import qualified CommonLogic.Parse_CLIF as CLIF (basicSpec)

import Syntax.AS_Library
import Syntax.AS_Structured

import Control.Monad (foldM)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe
import Data.List

import System.FilePath
import System.Directory (doesFileExist)

import Common.Http

type SpecMap = Map.Map FilePath SpecInfo
type SpecInfo = (BASIC_SPEC, Set.Set String, Set.Set FilePath)
                -- (spec, topTexts, importedBy)

-- | call for CommonLogic CLIF-parser with recursive inclusion of importations
parseCL_CLIF :: FilePath -> HetcatsOpts -> IO [LIB_DEFN]
parseCL_CLIF filename opts = do
  let dirFile@(dir, _) = splitFileName filename
  specMap <- downloadSpec opts Map.empty Set.empty Set.empty False dirFile dir
  return $ map convertToLibDefN $ topSortSpecs
    $ Map.map (\ (b, _, _) ->
               (b, Set.map (rmSuffix . tokStr) $ directImports b)) specMap

-- call for CommonLogic CLIF-parser for a single file
parseCL_CLIF_contents :: FilePath -> String -> Either ParseError [BASIC_SPEC]
parseCL_CLIF_contents = runParser (many $ CLIF.basicSpec Map.empty)
                        (emptyAnnos ())

{- maps imports in basic spec to global definition links (extensions) in
development graph -}
convertToLibDefN :: (BASIC_SPEC, FilePath) -> LIB_DEFN
convertToLibDefN (spec, fp) = let
  i = filePathToLibId $ rmSuffix fp
  in Lib_defn (iriLibName i)
    (makeLogicItem CommonLogic
    : map (addDownload False) (importsAsIris spec)
    ++ [convertToLibItem spec i])
    nullRange []

convertToLibItem :: BASIC_SPEC -> IRI -> Anno.Annoted LIB_ITEM
convertToLibItem b i = makeSpecItem i $ createSpec b

importsAsIris :: BASIC_SPEC -> [IRI]
importsAsIris =
  map (filePathToLibId . rmSuffix . tokStr) . Set.toList . directImports

createSpec :: BASIC_SPEC -> Anno.Annoted SPEC
createSpec b = addImports (importsAsIris b)
  . makeSpec $ G_basic_spec CommonLogic b

specNameL :: [BASIC_SPEC] -> String -> [String]
specNameL bs def = case bs of
  [_] -> [def]
  _ -> map (specName def) [0 .. (length bs)]

-- returns a unique name for a node
specName :: String -> Int -> String
specName def i = def ++ "_" ++ show i

fileCombine :: FilePath -> FilePath -> FilePath
fileCombine d = (\ s -> case s of
   '.' : p : r | isPathSeparator p -> r
   _ -> s) . combine d

httpCombine :: FilePath -> FilePath -> FilePath
httpCombine d f = if checkUri f then f else fileCombine d f

collectDownloads :: HetcatsOpts -> String -> SpecMap -> (String, SpecInfo)
                    -> IO SpecMap
collectDownloads opts baseDir specMap (n, (b, topTexts, importedBy)) = do
  let directImps = Set.elems $ Set.map tokStr $ directImports b
      newTopTexts = Set.insert n topTexts
      newImportedBy = Set.insert n importedBy
  foldM (\ sm d -> do
          let p@(ddir, _) = splitFileName d
              baseDir' = httpCombine baseDir ddir
          newDls <- downloadSpec opts sm newTopTexts newImportedBy True
              p baseDir'
          return (Map.unionWith unify newDls sm)
        ) specMap directImps -- imports get @n@ as new "importedBy"

downloadSpec :: HetcatsOpts -> SpecMap -> Set.Set String -> Set.Set String
                -> Bool -> (String, String) -> String -> IO SpecMap
downloadSpec opts specMap topTexts importedBy isImport dirFile baseDir = do
  let fn = rmSuffix $ uncurry fileCombine dirFile
  case Map.lookup fn specMap of
      Just info@(b, t, _)
        | isImport && Set.member fn importedBy
          -> error (concat [
                    "Illegal cyclic import: ", show (pretty importedBy), "\n"
                  , "Hets currently cannot handle cyclic imports "
                  , "of Common Logic files. "
                  , "If you really need them, send us a message at "
                  , "hets@informatik.uni-bremen.de, and we will fix it."
                ])
        | t == topTexts
          -> return specMap
        | otherwise ->
          let newInfo = unify info (b, topTexts, importedBy)
              newSpecMap = Map.insert fn newInfo specMap
          in collectDownloads opts baseDir newSpecMap (fn, newInfo)
      Nothing -> do
          contents <- getCLIFContents opts dirFile baseDir
          case parseCL_CLIF_contents fn contents of
              Left err -> error $ show err
              Right bs ->
                let nbs = zip (specNameL bs fn) bs
                    nbtis = map (\ (n, b) -> (n, (b, topTexts, importedBy))) nbs
                    newSpecMap = foldr (\ (n, bti) sm ->
                        Map.insertWith unify n bti sm
                      ) specMap nbtis
                in foldM (\ sm nbt -> do
                          newDls <- collectDownloads opts baseDir sm nbt
                          return (Map.unionWith unify newDls sm)
                      ) newSpecMap nbtis

unify :: SpecInfo -> SpecInfo -> SpecInfo
unify (_, s, p) (a, t, q) = (a, s `Set.union` t, p `Set.union` q)

{- one could add support for uri fragments/query
(perhaps select a text from the file) -}
getCLIFContents :: HetcatsOpts -> (String, String) -> String -> IO String
getCLIFContents opts dirFile baseDir =
  let fn = uncurry fileCombine dirFile
      uStr1 = useCatalogURL opts
        $ if checkUri baseDir then httpCombine baseDir fn else fn
      uStr = fromMaybe uStr1 $ stripPrefix "file://" uStr1
  in
  if checkUri uStr then getCLIFContentsHTTP opts uStr "" else
  localFileContents opts uStr baseDir

getCLIFContentsHTTP :: HetcatsOpts -> String -> String -> IO String
getCLIFContentsHTTP opts uriS extension = do
    let extUri = uriS ++ extension
    putIfVerbose opts 3 $ "Trying to download " ++ extUri
    res <- loadFromUri extUri
    case res of
        Right rb -> do
          putIfVerbose opts 2 $ "Downloaded " ++ extUri
          return rb
        Left err -> case extension of
          "" -> getCLIFContentsHTTP opts uriS ".clf"
          ".clf" -> getCLIFContentsHTTP opts uriS ".clif"
          _ -> error $ "File not found via HTTP: " ++ uriS
             ++ "[.clf | .clif]\n" ++ err

localFileContents :: HetcatsOpts -> String -> String -> IO String
localFileContents opts filename baseDir = do
  file <- findLibFile (baseDir : libdirs opts) filename
  putIfVerbose opts 2 $ "Reading CLIF file " ++ file
  readFile file

findLibFile :: [FilePath] -> String -> IO FilePath
findLibFile ds f = if checkUri f then return f else do
  e <- doesFileExist f
  if e then return f else findLibFileAux ds f

findLibFileAux :: [FilePath] -> String -> IO FilePath
findLibFileAux fps f = case fps of
  d : ds -> do
    let fs = [ fileCombine d $ addExtension f $ show $ CommonLogicIn b
             | b <- [False, True]]
    es <- mapM doesFileExist fs
    case filter fst $ zip es fs of
        [] -> findLibFileAux ds f
        (_, f0) : _ -> return f0
  [] -> error $ "Could not find Common Logic Library " ++ f

-- retrieves all importations from the text
directImports :: BASIC_SPEC -> Set.Set NAME
directImports (CL.Basic_spec items) = Set.unions
  $ map (getImports_textMetas . textsFromBasicItems . Anno.item) items

textsFromBasicItems :: BASIC_ITEMS -> [TEXT_META]
textsFromBasicItems (Axiom_items axs) = map Anno.item axs

getImports_textMetas :: [TEXT_META] -> Set.Set NAME
getImports_textMetas tms = Set.unions $ map (getImports_text . getText) tms

getImports_text :: TEXT -> Set.Set NAME
getImports_text txt = case txt of
  Text p _ -> Set.fromList $ map impName $ filter isImportation p
  Named_text _ t _ -> getImports_text t

isImportation :: PHRASE -> Bool
isImportation ph = case ph of
  Importation _ -> True
  _ -> False

impName :: PHRASE -> NAME
impName ph = case ph of
  Importation (Imp_name n) -> n
  _ -> error "CL.impName"

topSortSpecs :: Map.Map FilePath (BASIC_SPEC, Set.Set FilePath)
  -> [(BASIC_SPEC, FilePath)]
topSortSpecs specMap =
  let (fm, rm) = Map.partition (Set.null . snd) specMap
  in if Map.null fm then [] else
     map (\ (n, (b, _)) -> (b, n)) (Map.toList fm) ++ topSortSpecs
         (Map.map (\ (b, is) -> (b, is Set.\\ Map.keysSet fm)) rm)
