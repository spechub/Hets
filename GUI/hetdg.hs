
-- needs ghc and UniForM workbench
-- for the UniForM workbench:
-- cd into the folder where HetCATS lives
-- cvs co uni
-- configure
-- gmake boot
-- gmake packages

{- GUI/hetdg.hs
   $Id$
   Till Mossakowski

   Temporary interface for displaying development graphs.
   Should be replaced with hets in the future.
   
-}


module Main

where

import System.Environment
import Logic.LogicGraph
import Static.AnalysisLibrary
import System.IO
import Static.DotGraph

import GUI.ConvertDevToAbstractGraph

import GUI.AbstractGraphView

proceed fname showdg = do
  res <- anaFile logicGraph defaultLogic fname False
  case res of
    (_,Just (ln,dg,libenv)) -> 
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
