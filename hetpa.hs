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

parsefile fname = do
  input <- readFile fname
  case runParser (library logicGraph) defaultLogic fname input of
            Left err -> error (show err)
            Right x -> putStrLn (take 50 (show (printText0_eGA x)) ++ "\n...")

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


