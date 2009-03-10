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

import GMP.Generic
import GMP.Logics
import GMP.Parser
import GMP.Prover

-- | Replaces all disjunctions by conjunctions and normalizes negations -
-- | This is the form that the sequent calculus expects
preparse_seq :: (Logic a, Eq a, Show a) => L a -> L a
preparse_seq f = 
  let disj2conj w = case w of
                      And x y -> let a = disj2conj x
                                     b = disj2conj y
                                 in And a b
                      Or x y  -> let a = disj2conj x
                                     b = disj2conj y
                                 in Neg (And (Neg a) (Neg b))
                      Neg x   -> let a = disj2conj x
                                 in Neg a
                      M i x   -> M i $ (map disj2conj x)
                      x       -> x
      negNorm w = case w of
                    Neg (Neg x) -> negNorm x
                    Neg x       -> Neg $ negNorm x
                    M i x       -> M i $ (map negNorm x)
                    And x y     -> let a = negNorm x
                                       b = negNorm y
                                   in And a b
                    x           -> x -- there is no need for discussing "Or"
  in negNorm $ disj2conj f

-- | Runs the parser and the prover and prints the result(s) of obtained.
runLex :: (Logic a, Eq a, Show a) => Parser (L a) -> String -> IO ()
runLex p_rL input = run (do spaces
                            x <- p_rL 
                            eof
                            return x
                        ) input

run :: (Logic a, Eq a, Show a) => Parser (L a) -> String -> IO ()
run p_r input = case (parse p_r "" input) of
                  Left err -> do putStr "parse error at "
                                 print err
                  Right y ->  do let x = preparse_seq y
                                 -- show formula that is given to the sequent calculus
                                 putStrLn (show x)
                                 let isS = sequent_satisfiable x
                                 case isS of
                                    True -> putStrLn "... is Satisfiable"
                                    _    -> putStrLn "... is Not Satisfiable"
                                 let isP = sequent_provable x
                                 case isP of
                                    True -> putStrLn "... is Provable"
                                    _    -> putStrLn "... is Not Provable"

-- | Auxiliary run function for testing with the input given as string
runTest :: Int -> String -> IO ()
runTest ml input = do
    case ml of
     1 -> runLex ((parser Sqr parseKindex) :: Parser (L K)) input
     2 -> runLex ((parser Sqr parseKDindex) :: Parser (L KD)) input
     3 -> runLex ((parser Sqr parseCindex) :: Parser (L C)) input
     4 -> runLex ((parser Ang parseGindex) :: Parser (L G)) input
     5 -> runLex ((parser Ang parsePindex) :: Parser (L P)) input
     6 -> runLex ((parser Sqr parseHMindex) :: Parser (L HM)) input
     7 -> runLex ((parser Sqr parseMindex) :: Parser (L Mon)) input
     8 -> runLex ((parser Ang parseConindex) :: Parser (L Con)) input
     _ -> showHelp
    return ()
-- | Function for displying user help 
showHelp :: IO()
showHelp = do
    putStrLn ( "Usage:\n" ++
               "    ./main <ML> -p <path> or ./main <ML> -t <test>\n\n" ++
               "<ML>:    1 for K Modal Logic\n" ++
               "         2 for KD Modal Logic\n" ++
               "         3 for Coalition Logic\n" ++
               "         4 for Graded Modal Logic\n" ++
               "         5 for Probabilistic Modal Logic\n" ++
               "         6 for Hennessy-Milner Modal Logic\n" ++
               "         7 for Monotonic Modal Logic\n" ++
               "         8 for Conditional Modal Logic\n" ++
               "<path>:  path to input file\n" ++
               "<test>:  test given as a string\n")
-- | main program function
main :: IO()
main = do
    args <- getArgs
    if (args == [])||(head args == "--help")||(length args < 3)
     then showHelp
     else let ml:it:test:[] = take 3 args
          in case it of
               "-p" -> do input <- readFile test
                          runTest (read ml) input
               "-t" -> runTest (read ml) test
               _    -> showHelp
