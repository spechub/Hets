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
import DotGraph


proceed fname = do
  putStrLn ("Reading "++fname)
  dg <- ana_file logicGraph defaultLogic fname
  putStrLn ("Successfully analyzed.")
  h <- openFile (fname++".dot") WriteMode
  sequence (map (hPutStrLn h) (dot dg))
  hClose h


main = do
  files <- getArgs
  sequence (map proceed files)


