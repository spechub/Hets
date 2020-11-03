{- |
Module      :  ./CommonLogic/ParseCLAsLibDefn.hs
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
import Common.Parsec
import Common.Result
import Common.ResultT

import Driver.Options
import Driver.ReadFn

import Text.ParserCombinators.Parsec

import Logic.Grothendieck

import CommonLogic.AS_CommonLogic as CL
import CommonLogic.Logic_CommonLogic
import qualified CommonLogic.Parse_CLIF as CLIF (basicSpec)

import Syntax.AS_Library
import Syntax.AS_Structured

import Control.Monad (foldM)
import Control.Monad.Trans

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.List

import System.FilePath

type SpecMap = Map.Map FilePath SpecInfo
type SpecInfo = (BASIC_SPEC, FilePath, Set.Set String, Set.Set FilePath)
                -- (spec, topTexts, importedBy)

-- | call for CommonLogic CLIF-parser with recursive inclusion of importations
parseCL_CLIF :: FilePath -> HetcatsOpts -> ResultT IO [LIB_DEFN]
parseCL_CLIF filename opts = do
  let dirFile@(dir, _) = splitFileName filename
  specMap <- downloadSpec opts Map.empty Set.empty Set.empty False dirFile dir
  return $ map convertToLibDefN $ topSortSpecs
    $ Map.map (\ (b, f, _, _) ->
               (b, f, Set.map (rmSuffix . tokStr) $ directImports b)) specMap

-- call for CommonLogic CLIF-parser for a single file
parseCL_CLIF_contents :: FilePath -> String -> Either ParseError [BASIC_SPEC]
parseCL_CLIF_contents = runParser (many (CLIF.basicSpec Map.empty) << eof)
                        (emptyAnnos ())

{- maps imports in basic spec to global definition links (extensions) in
development graph -}
convertToLibDefN :: (FilePath, BASIC_SPEC, FilePath) -> LIB_DEFN
convertToLibDefN (fp, spec, realFp) = let
  i = filePathToLibId $ rmSuffix fp
  in Lib_defn (setFilePath realFp $ iriLibName i)
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
 -> ResultT IO SpecMap
collectDownloads opts baseDir specMap (n, (b, _, topTexts, importedBy)) = do
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

justErr :: a -> String -> ResultT IO a
justErr a s = liftR $ plain_error a s nullRange

downloadSpec :: HetcatsOpts -> SpecMap -> Set.Set String -> Set.Set String
  -> Bool -> (String, String) -> String -> ResultT IO SpecMap
downloadSpec opts specMap topTexts importedBy isImport dirFile baseDir = do
  let fn = rmSuffix $ uncurry httpCombine dirFile
  case Map.lookup fn specMap of
      Just info@(b, f, t, _)
        | isImport && Set.member fn importedBy ->
           justErr specMap . intercalate "\n "
             $ "unsupported cyclic imports:" : Set.toList importedBy
        | t == topTexts
          -> return specMap
        | otherwise ->
          let newInfo = unify info (b, f, topTexts, importedBy)
              newSpecMap = Map.insert fn newInfo specMap
          in collectDownloads opts baseDir newSpecMap (fn, newInfo)
      Nothing -> do
        mCont <- lift $ getCLIFContents opts dirFile baseDir
        case mCont of
          Left err -> justErr specMap $ show err
          Right (file, contents) -> do
            lift $ putIfVerbose opts 2 $ "Downloaded " ++ file
            case parseCL_CLIF_contents fn contents of
              Left err -> justErr specMap $ show err
              Right bs -> do
                let nbs = zip (specNameL bs fn) bs
                nbs2 <- mapM (\ (n, b) -> case
                    map (rmSuffix . tokStr) $ clTexts b of
                  [txt] -> if txt == fn then return (n, b) else
                    liftR $ justWarn (if isImport then n else txt, b)
                      $ "filename " ++ show fn
                        ++ " does not match cl-text " ++ show txt
                  [] -> liftR $ justWarn (n, b)
                    $ "missing cl-text in " ++ show fn
                  ts -> liftR $ justWarn (n, b)
                    $ "multiple cl-text entries in "
                      ++ show fn ++ "\n" ++ unlines (map show ts)
                  ) nbs
                let nbtis = map (\ (n, b) ->
                                 (n, (b, file, topTexts, importedBy))) nbs2
                    newSpecMap = foldr (\ (n, bti) sm ->
                        Map.insertWith unify n bti sm
                      ) specMap nbtis
                foldM (\ sm nbt -> do
                          newDls <- collectDownloads opts baseDir sm nbt
                          return (Map.unionWith unify newDls sm)
                      ) newSpecMap nbtis

unify :: SpecInfo -> SpecInfo -> SpecInfo
unify (_, _, s, p) (a, b, t, q) = (a, b, s `Set.union` t, p `Set.union` q)

{- one could add support for uri fragments/query
(perhaps select a text from the file) -}
getCLIFContents :: HetcatsOpts -> (String, String) -> String
  -> IO (Either String (FilePath, String))
getCLIFContents opts dirFile baseDir =
  let fn = uncurry httpCombine dirFile
      uStr = useCatalogURL opts
        $ if checkUri baseDir then httpCombine baseDir fn else fn
  in getExtContent opts { libdirs = baseDir : libdirs opts }
         [".clif", ".clf"] uStr

-- retrieves all importations from the text
directImports :: BASIC_SPEC -> Set.Set NAME
directImports (CL.Basic_spec items) = Set.unions
  $ map (getImports_textMetas . textsFromBasicItems . Anno.item) items

clTexts :: BASIC_SPEC -> [NAME]
clTexts (CL.Basic_spec items) =
  concatMap (getClTexts . textsFromBasicItems . Anno.item) items

textsFromBasicItems :: BASIC_ITEMS -> [TEXT_META]
textsFromBasicItems (Axiom_items axs) = map Anno.item axs

getImports_textMetas :: [TEXT_META] -> Set.Set NAME
getImports_textMetas = Set.unions . map (getImports_text . getText)

getClTexts :: [TEXT_META] -> [NAME]
getClTexts = concatMap (getClTextTexts . getText)

getClTextTexts :: TEXT -> [NAME]
getClTextTexts txt = case txt of
  Named_text n t _ -> n : getClTextTexts t
  _ -> []

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

topSortSpecs :: Map.Map FilePath (BASIC_SPEC, FilePath, Set.Set FilePath)
  -> [(FilePath, BASIC_SPEC, FilePath)]
topSortSpecs specMap =
  let (fm, rm) = Map.partition (\ (_, _, is) -> Set.null is) specMap
  in if Map.null fm then [] else
     map (\ (n, (b, f, _)) -> (n, b, f)) (Map.toList fm) ++ topSortSpecs
         (Map.map (\ (b, f, is) -> (b, f, is Set.\\ (Set.fromList $ Map.keys fm))) rm)
