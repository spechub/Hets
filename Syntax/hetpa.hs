module Main

where

import Syntax.Parse_AS_Structured
import System.Environment
import Common.Lib.Parsec
import Logic.LogicGraph
import Syntax.Print_HetCASL

parsefile fname = do
  input <- readFile fname
  case runParser (library logicGraph) defaultLogic fname input of
            Left err -> error (show err)
            Right x -> putStrLn (take 200 (show (printText0_eGA x)) ++ "\n...")


main = do
  files <- getArgs
  sequence (map parsefile files)


