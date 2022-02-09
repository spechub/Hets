{- |
Module      :  ./Driver/ReadFn.hs
Description :  reading and parsing ATerms, CASL, DOL files
Copyright   :  (c) Klaus Luettich, C. Maeder, Uni Bremen 2002-2014
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

reading and parsing ATerms, CASL, DOL files as much as is needed for the
static analysis
-}

module Driver.ReadFn
  ( findFileOfLibNameAux
  , libNameToFile
  , fileToLibName
  , readVerbose
  , guessXmlContent
  , isDgXmlFile
  , getContent
  , getExtContent
  , fromShATermString
  , getContentAndFileType
  , showFileType
  , keepOrigClifName
  ) where

import Logic.Grothendieck

import ATC.Grothendieck

import Driver.Options
import Driver.Version

import ATerm.AbstractSyntax
import ATerm.ReadWrite

import Common.Http
import Common.FileType
import Common.Id
import Common.IO
import Common.IRI
import Common.Result
import Common.ResultT
import Common.DocUtils
import Common.LibName
import Common.Utils

import Text.XML.Light

import System.FilePath
import System.Directory

import Control.Monad

import Data.Char (isSpace)
import Data.List (isPrefixOf)
import Data.Maybe

noPrefix :: QName -> Bool
noPrefix = isNothing . qPrefix

isDgXml :: QName -> Bool
isDgXml q = qName q == "DGraph" && noPrefix q

isPpXml :: QName -> Bool
isPpXml q = qName q == "Lib" && noPrefix q

isDMU :: QName -> Bool
isDMU q = qName q == "ClashResult" && noPrefix q

isRDF :: QName -> Bool
isRDF q = qName q == "RDF" && qPrefix q == Just "rdf"

isOWLOnto :: QName -> Bool
isOWLOnto q = qName q == "Ontology" && qPrefix q == Just "owl"

guessXmlContent :: Bool -> String -> Either String InType
guessXmlContent isXml str = case dropWhile isSpace str of
 '<' : _ -> case parseXMLDoc str of
  Nothing -> Right GuessIn
  Just e -> case elName e of
    q | isDgXml q -> Right DgXml
      | isRDF q -> Right $ OWLIn $ if any (isOWLOnto . elName) $ elChildren e
          then OwlXml else RdfXml
      | qName q == "Ontology" -> Right $ OWLIn OwlXml
      | isDMU q -> Left "unexpected DMU xml format"
      | isPpXml q -> Left "unexpected pp.xml format"
      | null (qName q) || not isXml -> Right GuessIn
      | otherwise -> Left $ "unknown XML format: " ++ tagEnd q ""
 _ -> Right GuessIn  -- assume that it is no xml content

isDgXmlFile :: HetcatsOpts -> FilePath -> String -> Bool
isDgXmlFile opts file content = guess file (intype opts) == DgXml
        && guessXmlContent True content == Right DgXml

readShATermFile :: ShATermLG a => LogicGraph -> FilePath -> IO (Result a)
readShATermFile lg fp = do
    str <- readFile fp
    return $ fromShATermString lg str

fromVersionedATT :: ShATermLG a => LogicGraph -> ATermTable -> Result a
fromVersionedATT lg att =
    case getATerm att of
    ShAAppl "hets" [versionno, aterm] [] ->
        if hetsVersionNumeric == snd (fromShATermLG lg versionno att)
        then Result [] (Just $ snd $ fromShATermLG lg aterm att)
        else Result [Diag Warning
                     "Wrong version number ... re-analyzing"
                     nullRange] Nothing
    _ -> Result [Diag Warning
                   "Couldn't convert ShATerm back from ATermTable"
                   nullRange] Nothing

fromShATermString :: ShATermLG a => LogicGraph -> String -> Result a
fromShATermString lg str = if null str then
    Result [Diag Warning "got empty string from file" nullRange] Nothing
    else fromVersionedATT lg $ readATerm str

readVerbose :: ShATermLG a => LogicGraph -> HetcatsOpts -> Maybe LibName
  -> FilePath -> IO (Maybe a)
readVerbose lg opts mln file = do
    putIfVerbose opts 2 $ "Reading " ++ file
    Result ds mgc <- readShATermFile lg file
    showDiags opts ds
    case mgc of
      Nothing -> return Nothing
      Just (ln2, a) -> case mln of
        Just ln | ln2 /= ln -> do
          putIfVerbose opts 0 $ "incompatible library names: "
               ++ showDoc ln " (requested) vs. "
               ++ showDoc ln2 " (found)"
          return Nothing
        _ -> return $ Just a

-- | create a file name without suffix from a library name
libNameToFile :: LibName -> FilePath
libNameToFile ln = maybe (libToFileName ln)
  (rmSuffix . iriToStringUnsecure) $ locIRI ln

findFileOfLibNameAux :: HetcatsOpts -> FilePath -> IO (Maybe FilePath)
findFileOfLibNameAux opts file = do
          let fs = map (</> file) $ "" : libdirs opts
          ms <- mapM (existsAnSource opts) fs
          return $ case catMaybes ms of
            [] -> Nothing
            f : _ -> Just f

-- | convert a file name that may have a suffix to a library name
fileToLibName :: HetcatsOpts -> FilePath -> LibName
fileToLibName opts efile =
    let paths = libdirs opts
        file = rmSuffix efile -- cut of extension
        pps = filter snd $ map (\ p -> (p, isPrefixOf p file)) paths
    in emptyLibName $ case pps of
         [] -> if useLibPos opts then convertFileToLibStr file
            else mkLibStr file
         (path, _) : _ -> mkLibStr $ drop (length path) file
                   -- cut off libdir prefix

-- | add query string for an access token before loading an URI
loadAccessUri :: HetcatsOpts -> FilePath -> IO (Either String String)
loadAccessUri opts fn = do
  let u = fn ++ case accessToken opts of
        "" -> ""
        t -> '?' : accessTokenS ++ "=" ++ t
  putIfVerbose opts 4 $ "downloading " ++ u
  loadFromUri opts u

downloadSource :: HetcatsOpts -> FilePath -> IO (Either String String)
downloadSource opts fn =
  if checkUri fn then loadAccessUri opts fn else do
    b <- doesFileExist fn
    if b then catchIOException (Left $ "could not read file: " ++ fn)
        . fmap Right $ readEncFile (ioEncoding opts) fn
      else return $ Left $ "file does not exist: " ++ fn

tryDownload :: HetcatsOpts -> [FilePath] -> FilePath
  -> IO (Either String (FilePath, String))
tryDownload opts fnames fn = case fnames of
  [] -> return $ Left $ "no input found for: " ++ fn
  fname : fnames' -> do
       let fname' = tryToStripPrefix "file://" fname
       mRes <- downloadSource opts fname'
       case mRes of
         Left err -> do
           eith <- tryDownload opts fnames' fn
           case eith of
             Left res | null fnames' ->
               return . Left $ err ++ "\n" ++ res
             _ -> return eith
         Right cont -> return $ Right (fname, cont)

getContent :: HetcatsOpts -> FilePath
  -> IO (Either String (FilePath, String))
getContent opts = getExtContent opts (getExtensions opts)

-- URIs must not have queries or fragments as possible extensions are appended
getExtContent :: HetcatsOpts -> [String] -> FilePath
  -> IO (Either String (FilePath, String))
getExtContent opts exts fp =
  let fn = tryToStripPrefix "file://" fp
      fs = getFileNames exts fn
      ffs = if checkUri fn || isAbsolute fn then fs else
           concatMap (\ d -> map (d </>) fs) $ "" : libdirs opts
  in tryDownload opts ffs fn

{- | output file type, checksum, real file name and file content.
inputs are hets options, optional argument for the file program,
and the library or file name. -}
getContentAndFileType :: HetcatsOpts -> FilePath
  -> IO (Either String (Maybe String, Maybe String, FileInfo, String))
getContentAndFileType opts fn = do
  eith <- getContent opts fn
  case eith of
    Left err -> return $ Left err
    Right (nFn, cont) -> do
      let isUri = checkUri nFn
      f <- if isUri then getTempFile cont "hets-file.tmp" else return nFn
      Result ds mr <- runResultT $ getMagicFileType (Just "--mime-type") f
      Result es mc <- runResultT $ getChecksum f
      showDiags opts (ds ++ es)
      let fInfo = FileInfo {
          wasDownloaded = isUri,
          filePath = if isUri then f else nFn
        }
      return $ Right (mr, mc, fInfo, cont)

showFileType :: HetcatsOpts -> FilePath -> IO ()
showFileType opts fn = do
  eith <- getContentAndFileType opts fn
  case eith of
    Left err -> hetsIOError err
    Right (mr, _, fInfo, _) ->
      let nFn = filePath fInfo
          fstr = (if nFn == fn then fn else nFn ++ " (via " ++ fn ++ ")")
             ++ ": "
      in case mr of
        Just s -> putStrLn $ fstr ++ s
        Nothing -> hetsIOError $ fstr ++ "could not determine file type."

keepOrigClifName :: HetcatsOpts -> FilePath -> FilePath -> FilePath
keepOrigClifName opts origName file =
  let iTypes = intype opts
  in case guess file iTypes of
       ext@(CommonLogicIn _) -> case guess origName iTypes of
         CommonLogicIn _ -> origName
         _ -> origName ++ '.' : show ext
       _ -> file
