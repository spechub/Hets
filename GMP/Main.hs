{- | Module     : $Header$
 -  Description : Implementation of main file for the prover
 -  Copyright   : (c) Georgel Calin & Lutz Schroeder, DFKI Lab Bremen
 -  License     : Similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
 -  Maintainer  : g.calin@jacobs-university.de
 -  Stability   : provisional
 -  Portability : portable
 -
 -  Provides the implementation of the user interaction "interface"
 -}
module Main where

import GenericSequent
import Parser

import System.Environment
import IO

-- | Map logic indexes from [Char] to Int
transformLogicIndex :: [Char] -> Int
transformLogicIndex c = case c of
                         "K"  -> 1
                         "KD" -> 2
                         "C"  -> 3
                         "G"  -> 4
                         "P"  -> 5
                         "HM" -> 6
                         "M"  -> 7
                         _    -> error "Main.transformLogicIndex"

-- | Function for displying user help 
showHelp :: IO()
showHelp = do
    putStrLn ( "Usage:\n" ++
               "    ./main -p <path> <N> <L1> <L2> .. <LN>\n" ++
               "    ./main -t <test> <N> <L1> <L2> .. <LN>\n\n" ++
               "<N>:     a natural number >0 specifing the number of combined/embedded logics\n" ++
               "<Lx>:    each logic can be one of the following cases:\n" ++
               "              K  - K Modal Logic\n" ++
               "              KD - KD Modal Logic\n" ++
               "              C  - Coalition Logic\n" ++
               "              G  - Graded Modal Logic\n" ++
               "              P  - Probability Logic\n" ++
               "              HM - Hennessy-Milner Modal Logic\n" ++
               "              M  - Monotonic Logic\n" ++
               "<path>:  path to input file\n" ++
               "<test>:  test given as a string\n")

-- | Main program function
main :: IO()
main = do
    args <- getArgs
    if (args == [])||(head args == "--help")||(length args < 4)
     then showHelp
     else let it:test:n:[] = take 3 args
              rest = tail.tail.tail $ args
          in if (length rest < read n)
             then showHelp
             else let list = take (read n) rest
                  in case it of
                       "-p" -> do test <- readFile test
                                  putStrLn test -- run prover with given input
                       "-t" -> putStrLn test -- run prover with given input
                       _    -> showHelp
