{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable(via imports)

Temporary interface for displaying development graphs.
   Should be replaced with hets in the future.
-}

-- needs ghc and UniForM workbench
-- for the UniForM workbench:
-- cd into the folder where HetCATS lives
-- cvs co uni
-- configure
-- gmake packages

module Main

where

import System.Environment
import qualified Common.Lib.Map as Map
import Static.AnalysisLibrary
import Static.DotGraph
import Static.DevGraph
import GUI.ShowGraph
import Driver.Options

process :: FilePath -> Bool -> IO ()
process fname showdg = do
  res <- anaLib defaultHetcatsOpts fname
  if showdg then showGraph fname defaultHetcatsOpts res
     else case res of
    Just (ln, lenv) -> case Map.lookup ln lenv of
        Nothing -> error "hetdg: lookup"
        Just gctx -> writeFile (fname++".dot") $ concat $ dot $ devGraph gctx
    _ -> return ()

main :: IO ()
main = do
  fn : opts <- getArgs
  process fn $ not $ opts == ["-dot"]
