{- |
Module      :  $Header$
Description :  run hets as server
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (via imports)

-}

module PGIP.Server where

import Driver.Options
import Driver.ReadFn

import Network.Wai.Handler.SimpleServer
import Network.Wai
import Network.Wai.Parse

import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.ByteString.Char8 as B8

import Static.ComputeTheory
import Static.DevGraph
import Static.PrintDevGraph
import Static.DotGraph
import Static.AnalysisLibrary
import Static.ToXml as ToXml

import Comorphisms.LogicGraph

import Text.XML.Light

import Common.DocUtils
import Common.LibName
import Common.Result
import Common.ResultT
import Common.ToXml
import Common.Utils

import Control.Monad.Trans (lift)
import Control.Monad

import qualified Data.IntMap as Map
import qualified Data.Set as Set
import Data.Char (isAlphaNum)
import Data.IORef
import Data.List
import Data.Ord
import Data.Graph.Inductive.Graph (lab)
import Data.Time.Clock

import System.Process
import System.Directory
import System.Exit
import System.FilePath

data Session = Session
  { sessLibEnv :: LibEnv
  , sessLibName :: LibName
  , previousKeys :: [Int]
  , sessStart :: UTCTime }

sessGraph :: Session -> DGraph
sessGraph (Session le ln _ _) = lookupDGraph ln le

hetsServer :: HetcatsOpts -> IO ()
hetsServer opts1 = do
  tempDir <- getTemporaryDirectory
  let tempHetsLib = tempDir </> "MyHetsLib"
      opts = opts1 { libdirs = tempHetsLib : libdirs opts1 }
  createDirectoryIfMissing False tempHetsLib
  sessRef <- newIORef Map.empty
  run 8000 $ \ re ->
    let query = B8.unpack $ queryString re in
    case B8.unpack (requestMethod re) of
    "GET" -> do
         let path = dropWhile (== '/') $ B8.unpack (pathInfo re)
         dirs@(_ : cs) <- getHetsLibContent opts path query
         if null cs then do
           Result ds ms <- getHetsResult opts sessRef path query
           return $ case ms of
             Nothing -> mkResponse status400
               $ showRelDiags 1 ds
             Just s -> mkOkResponse s
           else mkHtmlPage path dirs
    "POST" -> do
      (_, files) <- parseRequestBody tempFileSink re
      case files of
        [] -> return $ mkResponse status400 "no file uploaded"
        [(_, f)] -> do
           let fn = B8.unpack (fileName f)
           if any isAlphaNum fn then do
             copyFile (fileContent f) (tempHetsLib </> B8.unpack (fileName f))
             dirs <- getHetsLibContent opts "" query
             mkHtmlPage "" dirs
            else return $ mkResponse status400 $ "illegal file name: " ++ fn
        _ -> return $ mkResponse status400 $ "cannot handle multiple files "
              ++ show (map (fileName . snd) files)
    _ -> return $ mkResponse status405 ""

mkHtmlString :: FilePath -> [Element] -> String
mkHtmlString path dirs = htmlHead ++ mkHtmlElem
  ("Listing of" ++ if null path then " repository" else ": " ++ path)
  (headElems path ++ [unode "ul" dirs])

mkHtmlElem :: String -> [Element] -> String
mkHtmlElem title body = ppElement $ unode "html"
                [ unode "head" $ unode "title" title
                , unode "body" body ]

mkHtmlPage :: FilePath -> [Element] -> IO Response
mkHtmlPage path = return . mkOkResponse . mkHtmlString path

mkResponse :: Status -> String -> Response
mkResponse st = Response st [] . ResponseLBS . BS.pack

mkOkResponse :: String -> Response
mkOkResponse = mkResponse status200

getDGraph :: HetcatsOpts -> IORef (Map.IntMap Session) -> FilePath
  -> ResultT IO (Session, Int)
getDGraph opts sessRef file = case readMaybe file of
  Nothing -> do
    (ln, le) <- anaLibFileOrGetEnv logicGraph opts { outputToStdout = False }
      Set.empty emptyLibEnv emptyDG (fileToLibName opts file) file
    time <- lift getCurrentTime
    let sess = Session le ln [] time
    k <- lift $ atomicModifyIORef sessRef
      (\ m -> let k = Map.size m in (Map.insert k sess m, k))
    return (sess, k)
  Just k -> do
    m <- lift $ readIORef sessRef
    case Map.lookup k m of
      Nothing -> liftR $ fail "unknown development graph"
      Just sess -> return (sess, k)

getSVG :: FilePath -> DGraph -> ResultT IO String
getSVG file dg = do
    (exCode, out, err) <- lift $ readProcessWithExitCode "dot" ["-Tsvg"]
          $ dotGraph file False dg
    case exCode of
      ExitSuccess -> liftR $ extractSVG out
      _ -> fail err

extractSVG :: String -> Result String
extractSVG str = case parseXMLDoc str of
  Nothing -> fail "did not recognize svg element"
  Just e -> return $ showTopElement e

cmpFilePath :: FilePath -> FilePath -> Ordering
cmpFilePath f1 f2 = case comparing hasTrailingPathSeparator f2 f1 of
  EQ -> compare f1 f2
  c -> c

getHetsResult :: HetcatsOpts -> IORef (Map.IntMap Session) -> FilePath
  -> String -> IO (Result String)
getHetsResult opts sessRef file query =
  let callHets = getDGraph opts sessRef file
      getSessGraph = fmap (sessGraph . fst) callHets
  in
  runResultT $ case dropWhile (== '?') query of
    "svg" -> do
        dg <- getSessGraph
        getSVG file dg
    "" -> do
        (sess, k) <- callHets
        let ln = show $ sessLibName sess
        liftR $ return $ htmlHead ++ mkHtmlElem
           ("Current development graph for " ++ ln)
           (unode "strong" ("library " ++ ln) :
            map (\ d -> aRef ('/' : show k ++ "?" ++ d) d)
                displayTypes)
    "xml" -> do
        (sess, _) <- callHets
        liftR $ return $ ppTopElement $ ToXml.dGraph (sessLibEnv sess)
          $ sessGraph sess
    "menu" | file == "dg" -> return "displaying the possible menus (missing)"
    qstr -> let
      (kst, rst) = span (`notElem` "&;") qstr
      midstr = case stripPrefix "id=" $ drop 1 rst of
                 Nothing -> Nothing
                 Just idstr -> readMaybe idstr :: Maybe Int
      in case (kst, midstr) of
        ("edge", Just i) -> do
          dg <- getSessGraph
          case getDGLinksById (EdgeId i) dg of
            [e@(_, _, l)] -> return $ showLEdge e ++ "\n" ++ showDoc l ""
            [] -> fail $ "no edge found with id: " ++ show i
            _ -> fail $ "multiple edges found with id: " ++ show i
        (_, Just i) | elem kst ["node", "theory"] -> do
          dg <- getSessGraph
          case lab (dgBody dg) i of
            Nothing -> fail $ "no node id: " ++ show i
            Just dgnode -> return
              $ (if isDGRef dgnode then ("reference " ++) else
               if isInternalNode dgnode then ("internal " ++) else id)
              "node " ++ getDGNodeName dgnode ++ " " ++ show i ++ "\n"
               ++ if kst == "node" then showDoc dgnode ""
                  else showDoc (maybeResult $ getGlobalTheory dgnode) "\n"
        _ -> fail $ "unexpected query: " ++ qstr

getHetsLibContent :: HetcatsOpts -> String -> String -> IO [Element]
getHetsLibContent opts dir query = do
  let hlibs = libdirs opts
  ds <- if null dir then return hlibs else
       filterM doesDirectoryExist $ map (</> dir) hlibs
  fs <- fmap (sortBy cmpFilePath . filter (not . isPrefixOf ".") . concat)
    $ mapM getDirContents ds
  return $ map (mkHtmlRef query) $ getParent dir : fs

getParent :: String -> String
getParent = addTrailingPathSeparator . ("/" </>) . takeDirectory
  . dropTrailingPathSeparator

-- | a variant that adds a trailing slash
getDirContents :: FilePath -> IO [FilePath]
getDirContents d = do
    fs <- getDirectoryContents d
    mapM (\ f -> doesDirectoryExist (d </> f) >>= \ b -> return
            $ if b then addTrailingPathSeparator f else f) fs

aRef :: String -> String -> Element
aRef lnk txt = add_attr (mkAttr "href" lnk) $ unode "a" txt

mkHtmlRef :: String -> String -> Element
mkHtmlRef query entry = unode "dir" $ aRef (entry ++ query) entry

headElems :: String -> [Element]
headElems path = let d = "default" in unode "strong" "Choose query type:" :
  map (\ q -> aRef (if q == d then "/" </> path else '?' : q) q)
      (d : displayTypes) ++ [uploadHtml]

displayTypes :: [String]
displayTypes = ["svg", "xml"]

findDisplayTypes :: [[String]] -> Maybe String
findDisplayTypes = find (`elem` displayTypes) . map head

htmlHead :: String
htmlHead =
    let dtd = "PUBLIC \"-//W3C//DTD XHTML 1.0 Transitional//EN\""
        url = "\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd\""
    in concat ["<!DOCTYPE html ", dtd, " ", url, ">\n"]

inputNode :: Element
inputNode = unode "input" ()

uploadHtml :: Element
uploadHtml = add_attrs
  [ mkAttr "action" "/"
  , mkAttr "enctype" "multipart/form-data"
  , mkAttr "method" "post" ]
  $ unode "form"
  [ add_attrs
    [ mkAttr "type" "file"
    , mkAttr "name" "file"
    , mkAttr "size" "40"]
    inputNode
  , add_attrs
    [ mkAttr "type" "submit"
    , mkAttr "value" "submit"]
    inputNode ]
