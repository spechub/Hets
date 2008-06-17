{- | Module     : $Header$
 -  Description : Implemenation of main file for the prover
 -  Copyright   : (c) Georgel Calin & Lutz Schroeder, DFKI Lab Bremen
 -  License     : Similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
 -  Maintainer  : g.calin@jacobs-university.de
 -  Stability   : provisional
 -  Portability : portable
 -
 -  Provides the implementation of the user interaction "interface"
 -}
module Main where

import Text.ParserCombinators.Parsec
import System.Environment
import IO

import GMP.Parser
import GMP.Generic

-- | Runs the parser and the prover and prints the result(s) of obtained.
runLex :: (Eq a, Show a) => Parser (L a) -> String -> IO ()
runLex p input = run (do spaces
                         x <- p
                         eof
                         return x
                     ) input

run :: (Eq a, Show a) => Parser (L a) -> String -> IO ()
run p input = case (parse p "" input) of
                Left err -> do putStr "parse error at "
                               print err
                Right x ->  do putStrLn ("Input Formula: " ++ show x ++ " ...")
                               putStrLn ("......")
                {-
                               let sat = checkSAT x
                               if sat then putStrLn "... is Satisfiable"
                                      else putStrLn "... is not Satisfiable"
                                      -}

-- | Auxiliary run function for testing
runTest :: Int -> FilePath -> IO ()
runTest ml p = do
    input <- readFile (p)
    case ml of
     1 -> runLex ((par5er parseKindex) :: Parser (L K)) input
     2 -> runLex ((par5er parseKDindex) :: Parser (L KD)) input
     3 -> runLex ((par5er parseCindex) :: Parser (L C)) input
     4 -> runLex ((par5er parseGindex) :: Parser (L G)) input
     5 -> runLex ((par5er parsePindex) :: Parser (L P)) input
     6 -> runLex ((par5er parseHMindex) :: Parser (L HM)) input
     7 -> runLex ((par5er parseMindex) :: Parser (L Mon)) input
    return ()
-- | Function for displying user help
help :: IO()
help = do
    putStrLn ( "Usage:\n" ++
               "    ./main <ML> <path>\n\n" ++
               "<ML>:    1 for K Modal Logic\n" ++
               "         2 for KD Modal Logic\n" ++
               "         3 for Coalition Logic\n" ++
               "         4 for Graded Modal Logic\n" ++
               "         5 for Probability Logic\n" ++
               "         6 for Hennessy-Milner Modal Logic\n" ++
               "         7 for Monotonic Logic\n" ++
               "<path>:  path to input file\n" )
-- | main program function
main :: IO()
main = do
    args <- getArgs
    if (args == [])||(head args == "--help")||(length args < 2)
     then help
     else let ml = head args
              p = head (tail args)
          in runTest (read ml) p
