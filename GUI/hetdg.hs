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

import ConvertDevToAbstractGraph

import Char
import DaVinciGraph
import GraphDisp
import GraphConfigure
import AbstractGraphView
import IORef

import FiniteMap


type DGraphToAGraphNode = FiniteMap (LIB_NAME,Node) Descr
type DGraphToAGraphEdge = FiniteMap (LIB_NAME,Edge) Descr
type AGraphToDGraphNode = FiniteMap Descr (LIB_NAME,Node) 
type AGraphToDGraphEdge = FiniteMap Descr (LIB_NAME,Node) 


proceed fname = do
  putStrLn ("Reading "++fname)
  dg <- ana_file logicGraph defaultLogic fname
  -- g <- toGraph dg  
  gv <- initgraphs
  Result gid err <- AbstractGraphView.makegraph "Heterogeneous development graph"  
                     [] [] [] []
                     gv
  AbstractGraphView.redisplay gid gv
  return ()

main = do
  [file] <- getArgs
  proceed file
