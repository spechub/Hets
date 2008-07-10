module Main

where

import Syntax.Parse_AS_Library
import System.Environment
import Text.ParserCombinators.Parsec
import Common.AnnoState
import Common.DocUtils
import Comorphisms.LogicGraph
import Syntax.Print_AS_Library ()

parsefile :: FilePath -> IO ()
parsefile fname = do
  input <- readFile fname
  case runParser (library logicGraph)
           (emptyAnnos ()) fname input of
    Left err -> error $ show err
    Right x -> putStrLn $ shows (pretty x) "\n..."

main :: IO ()
main = do
  files <- getArgs
  mapM_ parsefile files
