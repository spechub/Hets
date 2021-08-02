{- |
Module      :  ./OWL2/scripts/runManchester.hs
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

script for running the manchester syntax parsing
-}

import System.Environment

import OWL2.ParseMS
import OWL2.Print ()
import OWL2.ManchesterPrint ()

import Common.DocUtils
import Common.Parsec

import Text.ParserCombinators.Parsec

processFile :: String -> IO ()
processFile file = do
  str <- readFile file
  case runParser (parseOntologyDocument mempty << eof) () file str of
    Right o -> print o
    Left err -> print err

main :: IO ()
main = do
  args <- getArgs
  mapM_ processFile args
