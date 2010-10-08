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

import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.ByteString.Char8 as B8

import Static.DevGraph
import Static.DotGraph
import Static.AnalysisLibrary
import Static.ToXml as ToXml

import Comorphisms.LogicGraph

import Text.XML.Light

import Common.LibName
import Common.Result
import Common.ResultT
import Common.ToXml

import Control.Monad.Trans (lift)
import Control.Monad

import qualified Data.Set as Set
import Data.List
import Data.Ord

import System.Process
import System.Directory
import System.Exit
import System.FilePath

hetsServer :: HetcatsOpts -> IO ()
hetsServer opts = run 8000 $ \ re ->
  case B8.unpack (requestMethod re) of
    "GET" -> do
         let path = dropWhile (== '/') $ B8.unpack (pathInfo re)
             query = B8.unpack $ queryString re
         dirs@(_ : cs) <- getHetsLibContent opts path query
         if null cs then do
           Result ds ms <- getHetsResult opts path query
           return $ case ms of
             Nothing -> mkResponse status400
               $ showRelDiags 1 ds
             Just s -> mkOkResponse s
           else return $ mkOkResponse $ htmlHead ++
                ppElement (unode "html"
                [ unode "head" $ unode "title" $ "Listing of"
                   ++ if null path then " repository" else ": " ++ path
                , unode "body" $ headElems path ++ [unode "ul" dirs]])
    _ -> return $ mkResponse status405 ""

mkResponse :: Status -> String -> Response
mkResponse st = Response st [] . ResponseLBS . BS.pack

mkOkResponse :: String -> Response
mkOkResponse = mkResponse status200

getDGraph :: HetcatsOpts -> FilePath -> ResultT IO (LibName, LibEnv, DGraph)
getDGraph opts file = do
  (ln, le) <- anaLibFileOrGetEnv logicGraph opts { verbose = 0 }
      Set.empty emptyLibEnv emptyDG (fileToLibName opts file) file
  return (ln, le, lookupDGraph ln le)

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

getHetsResult :: HetcatsOpts -> FilePath -> String -> IO (Result String)
getHetsResult opts file query = let callHets = getDGraph opts file in
  runResultT $ case dropWhile (== '?') query of
    qstr | elem qstr ["", "d"]
      -> do
        (_, _, dg) <- callHets
        getSVG file dg
    "xml" -> do
        (_, le, dg) <- callHets
        liftR $ return $ ppTopElement $ ToXml.dGraph le dg
    qstr -> fail $ "unexpected query type: " ++ qstr

getHetsLibContent :: HetcatsOpts -> String -> String -> IO [Element]
getHetsLibContent opts dir query = do
  let hlibs = libdirs opts
  ds <- if null dir then return hlibs else
       filterM doesDirectoryExist $ map (</> dir) hlibs
  fs <- fmap (sortBy cmpFilePath . filter (not . isPrefixOf ".") . concat)
    $ mapM getDirContents ds
  return $ map (mkHtmlRef query) $ getParent dir : fs

getParent :: String -> String
getParent = ("/" </>) . takeDirectory . dropTrailingPathSeparator

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
      (d : displayTypes)

displayTypes :: [String]
displayTypes = ["dg", "xml"]

findDisplayTypes :: [[String]] -> Maybe String
findDisplayTypes = find (`elem` displayTypes) . map head

htmlHead :: String
htmlHead =
    let dtd = "PUBLIC \"-//W3C//DTD XHTML 1.0 Transitional//EN\""
        url = "\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd\""
    in concat ["<!DOCTYPE html ", dtd, " ", url, ">\n"]
