module Main

where

import Parse_AS_Structured
import System
import Parsec
import LogicGraph
import Print_HetCASL
import DevGraph
import AnalysisLibrary
import IO
import AS_Library
import Graph
import DotGraph

import ConvertDevToAbstractGraph

import Char
import DaVinciGraph
import GraphDisp
import GraphConfigure
import AbstractGraphView
import IORef

import FiniteMap


proceed fname showdg = do
  res <- ana_file1 logicGraph defaultLogic fname
  case res of
    Nothing -> return ()
    Just (ln,dg,libenv) -> 
      if showdg then do
       (gid,gv,cmaps) <- convertGraph ln libenv
       AbstractGraphView.redisplay gid gv
       getLine
       return () 
      else do
        h <- openFile (fname++".dot") WriteMode
        sequence (map (hPutStrLn h) (dot dg))
        hClose h

main = do
  args <- getArgs
  proceed (head args) (null (tail args))
