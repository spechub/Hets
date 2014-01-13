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
import Common.IRI (simpleIdToIRI)
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
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.List

import System.FilePath (combine, splitFileName, addExtension)
import System.Directory (doesFileExist)

import Common.Http

type SpecMap = Map String SpecInfo
type SpecInfo = (BASIC_SPEC, Set String, Set String)
                -- (spec, topTexts, importedBy)

-- | call for CommonLogic CLIF-parser with recursive inclusion of importations
parseCL_CLIF :: FilePath -> HetcatsOpts -> IO LIB_DEFN
parseCL_CLIF filename opts = do
  let dirFile@(dir, _) = splitFileName filename
  specMap <- downloadSpec opts Map.empty Set.empty Set.empty False dirFile dir
  specs <- anaImports opts dir specMap
  return $ convertToLibDefN (convertFileToLibStr filename) specs


-- call for CommonLogic CLIF-parser for a single file
parseCL_CLIF_contents :: FilePath -> String -> Either ParseError [BASIC_SPEC]
parseCL_CLIF_contents = runParser (many $ CLIF.basicSpec Map.empty)
                        (emptyAnnos ())

{- maps imports in basic spec to global definition links (extensions) in
development graph -}
convertToLibDefN :: String -> [(BASIC_SPEC, NAME)] -> LIB_DEFN
convertToLibDefN fn specs = Lib_defn (emptyLibName fn)
    (makeLogicItem CommonLogic : map convertToLibItems specs)
    nullRange []

convertToLibItems :: (BASIC_SPEC, NAME) -> Anno.Annoted LIB_ITEM
convertToLibItems (b, n) = makeSpecItem (simpleIdToIRI n) $ createSpec b

createSpec :: BASIC_SPEC -> Anno.Annoted SPEC
createSpec b = addImports
  (map (simpleIdToIRI . cnvImportName) . Set.elems $ directImports b)
  . makeSpec $ G_basic_spec CommonLogic b

specNameL :: [BASIC_SPEC] -> String -> [String]
specNameL [_] def = [def]
specNameL bs def = map (specName def) [0 .. (length bs)]

-- returns a unique name for a node
specName :: String -> Int -> String
specName def i = def ++ "_" ++ show i

cnvImportName :: NAME -> NAME
cnvImportName = mkSimpleId . convertFileToLibStr . tokStr

httpCombine :: FilePath -> FilePath -> FilePath
httpCombine d f = if checkUri f then f else combine d f

collectDownloads :: HetcatsOpts -> String -> SpecMap -> (String, SpecInfo)
                    -> IO SpecMap
collectDownloads opts baseDir specMap (n, (b, topTexts, importedBy)) =
  let directImps = Set.elems $ Set.map tokStr $ directImports b
      newTopTexts = Set.insert n topTexts
      newImportedBy = Set.insert n importedBy
  in foldM (\ sm d -> do
          let (ddir, df) = splitFileName d
              baseDir' = httpCombine baseDir ddir
          newDls <- downloadSpec opts sm newTopTexts newImportedBy True
              ("", df) baseDir'
          return (Map.unionWith unify newDls sm)
        ) specMap directImps -- imports get @n@ as new "importedBy"

downloadSpec :: HetcatsOpts -> SpecMap -> Set String -> Set String
                -> Bool -> (String, String) -> String -> IO SpecMap
downloadSpec opts specMap topTexts importedBy isImport dirFile baseDir =
  let filename = uncurry combine dirFile in
  let fn = convertFileToLibStr filename in
  case Map.lookup fn specMap of
      Just (b, t, i)
        | isImport && Set.member (convertFileToLibStr filename) importedBy
          -> error (concat [
                    "Illegal cyclic import: ", show (pretty importedBy), "\n"
                  , "Hets currently cannot handle cyclic imports "
                  , "of Common Logic files. "
                  , "If you really need them, send us a message at "
                  , "hets@informatik.uni-bremen.de, and we will fix it."
                ])
        | t == topTexts
          -> return specMap
        | otherwise -> do
          let newTopTexts = t `Set.union` topTexts
          let newImportedBy = i `Set.union` importedBy
          let newSpecMap = Map.insert fn (b, newTopTexts, newImportedBy) specMap
          collectDownloads opts baseDir newSpecMap
                       (fn, (b, newTopTexts, newImportedBy))
      Nothing -> do
          contents <- getCLIFContents opts dirFile baseDir
          case parseCL_CLIF_contents filename contents of
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
  let fn = uncurry combine dirFile
      uStr1 = useCatalogURL opts
        $ if checkUri baseDir then httpCombine baseDir fn else fn
      uStr = fromMaybe uStr1 $ stripPrefix "file://" uStr1
  in
  if checkUri uStr then getCLIFContentsHTTP uStr "" else
  localFileContents opts uStr baseDir

getCLIFContentsHTTP :: String -> String -> IO String
getCLIFContentsHTTP uriS extension = do
    res <- loadFromUri $ uriS ++ extension
    case res of
        Right rb -> return rb
        Left err -> case extension of
          "" -> getCLIFContentsHTTP uriS ".clf"
          ".clf" -> getCLIFContentsHTTP uriS ".clif"
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
findLibFileAux [] f = error $ "Could not find Common Logic Library " ++ f
findLibFileAux (d : ds) f = do
  let fs = [ combine d $ addExtension f $ show $ CommonLogicIn b
           | b <- [False, True]]
  es <- mapM doesFileExist fs
  case filter fst $ zip es fs of
        [] -> findLibFileAux ds f
        (_, f0) : _ -> return f0

-- retrieves all importations from the text
directImports :: BASIC_SPEC -> Set NAME
directImports (CL.Basic_spec items) = Set.unions
  $ map (getImports_textMetas . textsFromBasicItems . Anno.item) items

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

anaImports :: HetcatsOpts -> String -> SpecMap -> IO [(BASIC_SPEC, NAME)]
anaImports opts baseDir specMap = do
  downloads <- foldM
    (\ sm nbt -> do
      newSpecs <- collectDownloads opts baseDir sm nbt
      return (Map.unionWith unify newSpecs sm)
    ) specMap $ Map.assocs specMap
  let specAssocs = Map.assocs downloads
  let sortedSpecs = sortBy usingImportedByCount specAssocs
      -- sort by putting the latest imported specs to the beginning
  return $ bsNamePairs sortedSpecs

-- not fast (O(n+m)), but reliable
usingImportedByCount :: (String, SpecInfo) -> (String, SpecInfo) -> Ordering
usingImportedByCount (_, (_, _, importedBy1)) (_, (_, _, importedBy2)) =
  compare (Set.size importedBy2) (Set.size importedBy1)

bsNamePairs :: [(String, SpecInfo)] -> [(BASIC_SPEC, NAME)]
bsNamePairs = foldr (\ (n, (b, _, _)) r -> (b, mkSimpleId n) : r) []
