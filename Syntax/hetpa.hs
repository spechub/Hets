{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
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
