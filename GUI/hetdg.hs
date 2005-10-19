{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
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
import Static.AnalysisLibrary
import Static.DotGraph

import GUI.ShowGraph

import Driver.Options

import qualified Common.Lib.Map as Map

process :: FilePath -> Bool -> IO ()
process fname showdg = do
  res <- anaLib defaultHetcatsOpts fname
  if showdg then showGraph fname defaultHetcatsOpts res
     else case res of
    Just (ln, lenv) -> case Map.lookup ln lenv of
        Nothing -> error "hetdg: lookup"
        Just (_,_,dg) -> writeFile (fname++".dot") $ concat $ dot dg
    _ -> return ()

main :: IO ()
main = do
  fn : opts <- getArgs
  process fn $ not $ opts == ["-dot"]
