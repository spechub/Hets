module Main

where

import Parse_AS_Structured
import System
import Parsec
import LogicGraph
import Print_HetCASL
import IO

parsefile fname = do
  input <- readFile fname
  case runParser (library logicGraph) defaultLogic fname input of
            Left err -> error (show err)
            Right x -> putStrLn (take 200 (show (printText0_eGA x)) ++ "\n...")


main = do
  files <- getArgs
  sequence (map parsefile files)


