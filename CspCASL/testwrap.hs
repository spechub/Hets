{- |
Module      :  $Header$
Copyright   :  (c) Andy Gimblett and Markus Roggenbach and Uni Bremen 2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  a.m.gimblett@swan.ac.uk
Stability   :  provisional
Portability :  portable

Test case wrapper for CspCASL specs and fragments.

This is a standalone `main' wrapper for CspCASL-related tests
performed locally to the CspCASL codebase.  It's probably only of
interest to the CspCASL maintainers.
-}

module Main where

import System.Environment
import System.IO
import Text.ParserCombinators.Parsec

import Common.AnnoState (emptyAnnos)
import Common.DocUtils

import CspCASL.Parse_CspCASL
import CspCASL.Print_CspCASL()

prettyCspCASLFromFile :: FilePath -> IO ()
prettyCspCASLFromFile fname
  = do input <- readFile fname
       putStr ("Input:\n" ++ input ++ "Pretty print:\n")
       case (runParser basicCspCaslSpec (emptyAnnos ()) fname input) of
           Left err -> do putStr "parse error at "
                          print err
           Right x  -> do putStrLn $ showDoc x ""
                          -- print x -- print parse tree

-- parseFiles: Given a list of filenames, parse each file in turn.

parseFiles :: [String] -> IO()
parseFiles arg = case arg of
    []            -> do putStr "" -- kinda stupid
    (path:others) -> do prettyCspCASLFromFile path
			parseFiles others

-- Main: - calls parser for each file passed in.

main :: IO ()
main = do filenames <- getArgs
          parseFiles filenames
