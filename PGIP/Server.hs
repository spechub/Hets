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

import Comorphisms.LogicGraph

import Text.XML.Light

import Common.Result
import Common.ResultT
import Common.ToXml

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
         dirs <- getHetsLibContent opts path
         if null dirs then do
           Result ds ms <- getGraph opts path
           return $ case ms of
             Nothing -> mkResponse status400
               $ showRelDiags 1 ds
             Just s -> mkOkResponse s
           else return $ mkOkResponse $ htmlHead ++
                unlines (map showElement dirs)
    _ -> return $ mkResponse status405 ""

mkResponse :: Status -> String -> Response
mkResponse st = Response st [] . ResponseLBS . BS.pack

mkOkResponse :: String -> Response
mkOkResponse = mkResponse status200

getGraph :: HetcatsOpts -> FilePath -> IO (Result String)
getGraph opts file = runResultT $ do
  (ln, le) <- anaLibFileOrGetEnv logicGraph opts { verbose = 0 }
      Set.empty emptyLibEnv emptyDG (fileToLibName opts file) file
  let dg = lookupDGraph ln le
  (exCode, out, err) <- lift $ readProcessWithExitCode "dot" ["-Tsvg"]
      $ dotGraph file False dg
  case exCode of
      ExitSuccess -> liftR $ extractSVG out
      _ -> fail err

extractSVG :: String -> Result String
extractSVG str = case parseXMLDoc str of
  Nothing -> fail "did not recognize svg element"
  Just e -> return $ showTopElement e

getHetsLibContent :: HetcatsOpts -> String -> IO [Element]
getHetsLibContent opts dir = do
  let hlibs = libdirs opts
  ds <- if null dir then return hlibs else
       filterM doesDirectoryExist $ map (</> dir) hlibs
  fmap (map mkHtmlRef . sort . filter (not . isPrefixOf ".") . concat)
    $ mapM getDirContents ds

-- | a variant that adds a trailing slash
getDirContents :: FilePath -> IO [FilePath]
getDirContents d = do
    fs <- getDirectoryContents d
    mapM (\ f -> doesDirectoryExist (d </> f) >>= \ b -> return
            $ if b then addTrailingPathSeparator f else f) fs

mkHtmlRef :: String -> Element
mkHtmlRef entry = unode "br"
   $ add_attr (mkAttr "href" entry)
         $ unode "a" entry

htmlHead :: String
htmlHead =
    let dtd = "PUBLIC \"-//W3C//DTD XHTML 1.0 Transitional//EN\""
        url = "\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd\""
    in concat ["<!DOCTYPE html ", dtd, " ", url, ">\n"]
