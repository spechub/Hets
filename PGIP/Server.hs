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

import Control.Monad.Trans

import qualified Data.Set as Set

import System.Process
import System.Exit

hetsServer :: HetcatsOpts -> IO ()
hetsServer opts = run 8000 $ \ re ->
  case B8.unpack (requestMethod re) of
    "GET" -> do
       Result ds ms <-
         getGraph opts $ dropWhile (== '/') $ B8.unpack (pathInfo re)
       return $ case ms of
         Nothing -> Response status400 [] $ ResponseLBS $ BS.pack
           $ showRelDiags 1 ds
         Just s -> Response status200 [] $ ResponseLBS $ BS.pack s
    _ -> return $ Response status405 [] $ ResponseLBS BS.empty

getGraph :: HetcatsOpts -> FilePath -> IO (Result String)
getGraph opts file = runResultT $ do
  (ln, le) <- anaLibFileOrGetEnv logicGraph opts { verbose = 0 }
      Set.empty emptyLibEnv emptyDG (fileToLibName opts file) file
  let dg = lookupDGraph ln le
  (exCode, out, err) <- lift $ readProcessWithExitCode "dot" ["-Tsvg"]
      $ dotGraph False dg
  case exCode of
      ExitSuccess -> liftR $ extractSVG out
      _ -> fail err

extractSVG :: String -> Result String
extractSVG str = case parseXMLDoc str of
  Nothing -> fail "did not recognize svg element"
  Just e -> return $ showTopElement e
