{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable(via imports

   Temporary interface for displaying development graphs.
   Should be replaced with hets in the future.
   
-}

-- needs ghc and UniForM workbench
-- for the UniForM workbench:
-- cd into the folder where HetCATS lives
-- cvs co uni
-- configure
-- gmake boot
-- gmake packages


module Main

where

import System.Environment
import Comorphisms.LogicGraph
import Static.AnalysisLibrary
import System.IO
import Static.DotGraph

import GUI.ConvertDevToAbstractGraph

import GUI.AbstractGraphView
import Driver.Options

import Static.DevGraph

import Data.Char
import DaVinciGraph
import GraphDisp
import Data.IORef

proceed fname showdg = do
  res <- anaFile logicGraph defaultLogic defaultHetcatsOpts emptyLibEnv fname 
  case res of
    Just (ln,_,dg,libenv) -> 
      if showdg then do
       graphMem <- initializeConverter
       (gid,gv,cmaps) <- convertGraph graphMem ln libenv
       GUI.AbstractGraphView.redisplay gid gv
       getLine
       return () 
      else do
        h <- openFile (fname++".dot") WriteMode
        sequence (map (hPutStrLn h) (dot dg))
        hClose h
    _ -> return ()

main = do
  args <- getArgs
  proceed (head args) (not ((tail args)==["-dot"]))
