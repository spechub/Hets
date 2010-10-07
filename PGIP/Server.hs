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

import Common.Result
import Common.ResultT
import Common.ToXml
import Common.Utils

import Control.Monad.Trans (lift)
import Control.Monad

import qualified Data.Set as Set
import Data.List

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
         dirs <- getHetsLibContent opts path query
         if null dirs then do
           Result ds ms <- getGraph opts path query
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

getGraph :: HetcatsOpts -> FilePath -> String -> IO (Result String)
getGraph opts file query = runResultT $ do
  (ln, le) <- anaLibFileOrGetEnv logicGraph opts { verbose = 0 }
      Set.empty emptyLibEnv emptyDG (fileToLibName opts file) file
  let dg = lookupDGraph ln le
      qstr = dropWhile (== '?') query
      qs = splitOn '&' qstr
      qqs = map (splitOn '=') qs
  case findDisplayTypes qqs of
    Just str -> case str of
      "dg" -> do
        (exCode, out, err) <- lift $ readProcessWithExitCode "dot" ["-Tsvg"]
          $ dotGraph file False dg
        case exCode of
          ExitSuccess -> liftR $ extractSVG out
          _ -> fail err
      "xml" -> liftR $ return $ ppTopElement $ ToXml.dGraph le dg
      _ -> error "getGraph"
    Nothing -> fail "no query type chosen"

extractSVG :: String -> Result String
extractSVG str = case parseXMLDoc str of
  Nothing -> fail "did not recognize svg element"
  Just e -> return $ showTopElement e

getHetsLibContent :: HetcatsOpts -> String -> String -> IO [Element]
getHetsLibContent opts dir query = do
  let hlibs = libdirs opts
  ds <- if null dir then return hlibs else
       filterM doesDirectoryExist $ map (</> dir) hlibs
  fmap (map (mkHtmlRef query) . sort . filter (not . isPrefixOf ".") . concat)
    $ mapM getDirContents ds

-- | a variant that adds a trailing slash
getDirContents :: FilePath -> IO [FilePath]
getDirContents d = do
    fs <- getDirectoryContents d
    mapM (\ f -> doesDirectoryExist (d </> f) >>= \ b -> return
            $ if b then addTrailingPathSeparator f else f) fs

mkHtmlRef :: String -> String -> Element
mkHtmlRef query entry = unode "li"
   $ add_attr (mkAttr "href" $ entry ++ query)
         $ unode "a" entry

headElems :: String -> [Element]
headElems path = let d = "default" in unode "strong" "Choose query type:" :
  map (\ q -> add_attr (mkAttr "href"
                       $ if q == d then "/" </> path else '?' : q)
      $ unode "a" q) (d : displayTypes)

displayTypes :: [String]
displayTypes = ["dg", "xml"]

findDisplayTypes :: [[String]] -> Maybe String
findDisplayTypes = find (`elem` displayTypes) . map head

htmlHead :: String
htmlHead =
    let dtd = "PUBLIC \"-//W3C//DTD XHTML 1.0 Transitional//EN\""
        url = "\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd\""
    in concat ["<!DOCTYPE html ", dtd, " ", url, ">\n"]
