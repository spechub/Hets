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

--import ConvertDevToAbstractGraph

import Char
import DaVinciGraph
import GraphDisp
import GraphConfigure
import AbstractGraphView
import IORef

import FiniteMap


proceed fname = do
  dg <- ana_file1 logicGraph defaultLogic fname
  -- g <- toGraph dg  
  -- gv <- initgraphs
  {- Result gid err <- AbstractGraphView.makegraph "Heterogeneous development graph"  
                     [] [] [] []
                     gv
  AbstractGraphView.redisplay gid gv
  return () -}
  h <- openFile (fname++".dot") WriteMode
  sequence (map (hPutStrLn h) (dot dg))
  hClose h

main = do
  [file] <- getArgs
  proceed file
