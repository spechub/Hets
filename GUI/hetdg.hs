module Main

where

import System.Environment
import Syntax.LogicGraph
import Static.AnalysisLibrary
import System.IO
import Static.DotGraph

import GUI.ConvertDevToAbstractGraph

import Data.Char
import DaVinciGraph
import GraphDisp
import GUI.AbstractGraphView
import Data.IORef


proceed fname showdg = do
  res <- ana_file1 logicGraph defaultLogic fname
  case res of
    Nothing -> return ()
    Just (ln,dg,libenv) -> 
      if showdg then do
       (gid,gv,cmaps) <- convertGraph ln libenv
       GUI.AbstractGraphView.redisplay gid gv
       getLine
       return () 
      else do
        h <- openFile (fname++".dot") WriteMode
        sequence (map (hPutStrLn h) (dot dg))
        hClose h

main = do
  args <- getArgs
  proceed (head args) (null (tail args))
