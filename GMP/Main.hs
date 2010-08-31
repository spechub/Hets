{- | Module     : $Header$
 -  Description : Implementation of main file for the prover
 -  Copyright   : (c) Georgel Calin & Lutz Schroeder, DFKI Lab Bremen
 -  License     : GPLv2 or higher, see LICENSE.txt
 -  Maintainer  : g.calin@jacobs-university.de
 -  Stability   : provisional
 -  Portability : portable
 -
 -  Provides the implementation of the user interaction "interface"
 -}
module Main where

import GenericSequent
import ModalLogic
import CombLogic
import Parser

import Text.ParserCombinators.Parsec
import System.Environment
import IO

-- | Main parsing unit for checking provability/satisfiability
run :: (Eq a, Form a b c) => Parser (Boole a) -> String -> IO ()
run parser input =
  case (parse parser "" input) of
    Left err -> do putStr "parse error at "
                   print err
    Right x ->  do --putStrLn (show x{-++" <=> "++input-})
                   let isP = provable x
                   case isP of
                     True -> putStrLn "... is Provable"
                     _    -> let isS = sat x
                             in case isS of
                                  True -> putStrLn ("... is not Provable" ++
                                                    " but Satisfiable")
                                  _    -> putStrLn "... is not Satisfiable"

-- | Runs the main parsing unit (probably superfluous)
runLex :: (Eq a, Form a b c) => Parser (Boole a) -> String -> IO ()
runLex parser input = run (do spaces
                              res <- parser
                              eof
                              return res
                          ) input

-- | Auxiliary run function for testing with the input given as string
runTest :: [Int] -> String -> IO ()
runTest logics input =
  do {-case (head logics) of
       1 -> runLex (parseKindex{-(par5er Sqr parseKindex) :: Parser (L K)-}) input
       2 -> runLex ((par5er Sqr parseKDindex) :: Parser (L KD)) input
       3 -> runLex ((par5er Sqr parseCindex) :: Parser (L C)) input
       4 -> runLex ((par5er Ang parseGindex) :: Parser (L G)) input
       5 -> runLex ((par5er Ang parsePindex) :: Parser (L P)) input
       6 -> runLex ((par5er Sqr parseHMindex) :: Parser (L HM)) input
       7 -> runLex ((par5er Sqr parseMindex) :: Parser (L Mon)) input
       _ -> showHelp
     -}
     return ()

-- | Map logic indexes from [Char] to Int
indexToInt :: [Char] -> Int
indexToInt c = case c of
                 "K"  -> 1; "KD" -> 2
                 "C"  -> 3; "G"  -> 4
                 "P"  -> 5; "HM" -> 6
                 "M"  -> 7; _    -> error "Main.indexToInt"

-- | Function for displying user help
showHelp :: IO()
showHelp = do
    putStrLn ( "Usage:\n" ++
               "    ./main -p <path> <N> <L1> <L2> .. <LN>\n" ++
               "    ./main -t <test> <N> <L1> <L2> .. <LN>\n\n" ++
               "<N>:     a natural number >0 specifing the number of " ++
                        "combined/embedded logics\n" ++
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
                       "-p" -> do let logics = map indexToInt rest
                                  test <- readFile test
                                  putStrLn test -- run prover with given input
                                  putStrLn $ show logics
                       "-t" -> do let logics = map indexToInt rest
                                  putStrLn test -- run prover with given input
                                  putStrLn $ show logics
                       _    -> showHelp
