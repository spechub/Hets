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

import Text.ParserCombinators.Parsec
import System.Environment
import IO

--import Parser
import GenericSequent
{-

-- | Replaces all conjunctions by disjunctions and normalizes negations
preparse :: L a -> L a
preparse f = 
  let conj2disj w = case w of
                      And x y -> let a = conj2disj x
                                     b = conj2disj y
                                 in Neg (Or (Neg a) (Neg b))
                      Or x y  -> let a = conj2disj x
                                     b = conj2disj y
                                 in Or a b
                      Neg x   -> let a = conj2disj x
                                 in Neg a
                      M i x   -> M i $ conj2disj x
                      x       -> x
      negNorm w = case w of
                    Neg (Neg x) -> negNorm x
                    Neg x       -> Neg $ negNorm x
                    M i x       -> M i $ negNorm x
                    Or x y      -> let a = negNorm x
                                       b = negNorm y
                                   in Or a b
                    x           -> x -- there is no need for discussing "And"
  in negNorm $ conj2disj f
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
                  Right y ->  do let x = preparse y
                                 --putStrLn (show x{-++" <=> "++input-})
                                 let isP = provable x
                                 case isP of
                                    True -> putStrLn "... is Provable"
                                    _    -> let isS = sat x
                                            in case isS of
                                                 True -> putStrLn "... is not Provable but Satisfiable"
                                                 _    -> putStrLn "... is not Satisfiable"

-- | Auxiliary run function for testing with the input given as string
runTest :: [Int] -> String -> IO ()
runTest ml input = do
    case (head ml) of
     1 -> runLex ((par5er Sqr parseKindex) :: Parser (L K)) input
     2 -> runLex ((par5er Sqr parseKDindex) :: Parser (L KD)) input
     3 -> runLex ((par5er Sqr parseCindex) :: Parser (L C)) input
     4 -> runLex ((par5er Ang parseGindex) :: Parser (L G)) input
     5 -> runLex ((par5er Ang parsePindex) :: Parser (L P)) input
     6 -> runLex ((par5er Sqr parseHMindex) :: Parser (L HM)) input
     7 -> runLex ((par5er Sqr parseMindex) :: Parser (L Mon)) input
     _ -> showHelp
    return ()
-}
-- | Function for displying user help 
showHelp :: IO()
showHelp = do
    putStrLn ( "Usage:\n" ++
               "    ./main -p <path> <N> <L1> <L2> .. <LN>\n" ++
               "    ./main -t <test> <N> <L1> <L2> .. <LN>\n\n" ++
               "<N>:     a natural number >0 specifing the number of combined/embedded logics\n" ++
               "<Lx>:    each logic can be one of the following cases:\n" ++
               "              1 - K Modal Logic\n" ++
               "              2 - KD Modal Logic\n" ++
               "              3 - Coalition Logic\n" ++
               "              4 - Graded Modal Logic\n" ++
               "              5 - Probability Logic\n" ++
               "              6 - Hennessy-Milner Modal Logic\n" ++
               "              7 - Monotonic Logic\n" ++
               "<path>:  path to input file\n" ++
               "<test>:  test given as a string\n")
-- | main program function
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
                       "-p" -> do input <- readFile test
                                  putStrLn input
                       "-t" -> putStrLn test
                       _    -> showHelp
