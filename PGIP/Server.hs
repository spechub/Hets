{- |
Module      :  $Header$
Description :  run hets as server
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (via imports)

-}

module PGIP.Server (hetsServer) where

import PGIP.Query

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

import Interfaces.Command
import Interfaces.CmdAction

import Comorphisms.LogicGraph

import Text.XML.Light

import Common.DocUtils
import Common.LibName
import Common.Result
import Common.ResultT
import Common.ToXml

import Control.Monad.Trans (lift)
import Control.Monad

import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import Data.Char
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
  , _sessStart :: UTCTime }

sessGraph :: DGQuery -> Session -> Maybe DGraph
sessGraph dgQ (Session le ln _ _) = case dgQ of
  DGQuery _ (Just path) ->
      fmap snd $ find (\ (n, _) -> show (getLibId n) == path)
        $ Map.toList le
  _ -> Map.lookup ln le

hetsServer :: HetcatsOpts -> IO ()
hetsServer opts1 = do
  tempDir <- getTemporaryDirectory
  let tempHetsLib = tempDir </> "MyHetsLib"
      opts = opts1 { libdirs = tempHetsLib : libdirs opts1 }
  createDirectoryIfMissing False tempHetsLib
  sessRef <- newIORef IntMap.empty
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

addNewSess :: IORef (IntMap.IntMap Session) -> Session -> IO Int
addNewSess sessRef sess = atomicModifyIORef sessRef
      (\ m -> let k = IntMap.size m in (IntMap.insert k sess m, k))

getDGraph :: HetcatsOpts -> IORef (IntMap.IntMap Session) -> DGQuery
  -> ResultT IO (Session, Int)
getDGraph opts sessRef dgQ = case dgQ of
  NewDGQuery file -> do
    (ln, le) <- anaLibFileOrGetEnv logicGraph opts { outputToStdout = False }
      Set.empty emptyLibEnv emptyDG (fileToLibName opts file) file
    time <- lift getCurrentTime
    let sess = Session le ln [] time
    k <- lift $ addNewSess sessRef sess
    return (sess, k)
  DGQuery k _ -> do
    m <- lift $ readIORef sessRef
    case IntMap.lookup k m of
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

getHetsResult :: HetcatsOpts -> IORef (IntMap.IntMap Session) -> FilePath
  -> String -> IO (Result String)
getHetsResult opts sessRef file query =
  runResultT $ case anaUri file $ dropWhile (== '?')
                 $ filter (not . isSpace) query of
    Left err -> fail err
    Right (Query dgQ qk) -> do
      sk@(sess, k) <- getDGraph opts sessRef dgQ
      case sessGraph dgQ sess of
        Nothing -> fail $ "unknown library given by: " ++ file
        Just dg ->
          case qk of
            DisplayQuery ms -> case ms of
              Just "svg" -> getSVG file dg
              Just "xml" -> liftR $ return $ ppTopElement
                $ ToXml.dGraph (sessLibEnv sess) dg
              _ -> liftR $ return $ sessAns sk
            GlobCmdQuery s ->
              case find ((s ==) . cmdlGlobCmd . fst) allGlobLibAct of
              Nothing -> fail "getHetsResult.GlobCmdQuery"
              Just (_, act) -> do
                newLib <- liftR $ act (sessLibName sess) $ sessLibEnv sess
                let newSess = sess
                      { sessLibEnv = newLib
                      , previousKeys = k : previousKeys sess }
                nk <- lift $ addNewSess sessRef newSess
                liftR $ return $ sessAns (newSess, nk)
            NodeQuery i ms -> case lab (dgBody dg) i of
              Nothing -> fail $ "no node id: " ++ show i
              Just dgnode -> return
                $ (if isDGRef dgnode then ("reference " ++) else
                  if isInternalNode dgnode then ("internal " ++) else id)
                  "node " ++ getDGNodeName dgnode ++ " " ++ show i ++ "\n"
                  ++ case ms of
                       Just "theory" ->
                           showDoc (maybeResult $ getGlobalTheory dgnode) "\n"
                       _ -> showDoc dgnode ""
            EdgeQuery i _ ->
              case getDGLinksById i dg of
              [e@(_, _, l)] -> return $ showLEdge e ++ "\n" ++ showDoc l ""
              [] -> fail $ "no edge found with id: " ++ showEdgeId i
              _ -> fail $ "multiple edges found with id: " ++ showEdgeId i

sessAns :: (Session, Int) -> String
sessAns (sess, k) =
  let libName = sessLibName sess
      libEnv = sessLibEnv sess
      ln = show $ getLibId libName
      ref d = aRef ('/' : show k ++ "?" ++ d) d
      dg = lookupDGraph libName libEnv
      libref l = let s = show (getLibId l) in
        aRef ('/' : s ++ "?dg=" ++ show k ++ "&xml") s
      noderef f (n, lbl) = let s = show n in
        aRef ('/' : show k ++ f ++ s) $ s ++ " " ++ getDGNodeName lbl
      nRef n = [noderef "?node=" n, unode "strong" "---"
               , noderef "?theory=" n]
      edgeref e@(_, _, lbl) =
        aRef ('/' : show k ++ "?edge=" ++ showEdgeId (dgl_id lbl))
                 $ showLEdge e
  in htmlHead ++ mkHtmlElem
           ('(' : shows k ")" ++ ln)
           (unode "strong" ("library " ++ ln) :
            map ref displayTypes ++ [unode "p" "commands:"]
            ++ [unode "ul" $
                map (unode "li" . ref) globalCommands]
            ++ [unode "p" "imported libraries:"]
            ++ [unode "ul" $
                map (unode "li" . libref) $ Map.keys libEnv]
            ++ [unode "p" "nodes with local and global theories:"]
            ++ [unode "ul" $
                map (unode "li" . nRef) $ labNodesDG dg]
            ++ [unode "p" "edges:"]
            ++ [unode "ul" $
                map (unode "li" . edgeref) $ labEdgesDG dg]
           )

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
