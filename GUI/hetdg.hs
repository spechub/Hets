module Main

where

import Syntax.Parse_AS_Structured
import System.Environment
import Common.Lib.Parsec
import Syntax.LogicGraph
import Syntax.Print_HetCASL
import Static.DevGraph
import Static.AnalysisLibrary
import System.IO
import Syntax.AS_Library
import Common.Lib.Graph
import Static.DotGraph

import GUI.ConvertDevToAbstractGraph

import Data.Char
import DaVinciGraph
import GraphDisp
import GraphConfigure
import GUI.AbstractGraphView
import Data.IORef

import FiniteMap


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
