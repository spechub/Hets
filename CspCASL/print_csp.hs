{- |
Module      :  $Header$
Copyright   :  (c) Daniel Pratsch and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

testing file for CSP-CASL semantics
-}

module Main where

import CspCASL.Parse_AS_CSP_CASL
import CspCASL.Print_AS_CSP_CASL ()

import Common.DocUtils
import Common.AnnoState

import Text.ParserCombinators.Parsec
import System.IO
import System.Environment

run :: Pretty a => AParser () a -> String -> IO ()
run p input
        = case (runParser p (emptyAnnos ()) "" input) of
            Left err -> do { putStr "parse error at "
                           ; print err
                           }
            Right x -> putStrLn $ showDoc x ""

main :: IO ()
main = do { l <- getArgs
          ; c <- readFile (head l)
          ; run interim c
          }
