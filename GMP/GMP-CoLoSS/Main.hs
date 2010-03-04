{- | Module     : $Header$
 -  Description : Implemenation of main file for the prover
 -  Copyright   : (c) Georgel Calin & Lutz Schroeder, DFKI Lab Bremen
 -  License     : Similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
 -  Maintainer  : daniel.hausmann@dfki.de
 -  Stability   : provisional
 -  Portability : portable
 -
 -  Provides the implementation of the user interaction "interface"
 -}

module Main where

import Text.ParserCombinators.Parsec
import System.Environment
import IO

import GMP.Logics.Generic
import GMP.Parser
import GMP.Prover

--------------------------------------------------------------------------------
-- make use of these logics:
--------------------------------------------------------------------------------

import GMP.Logics.K
import GMP.Logics.KD
import GMP.Logics.HM
import GMP.Logics.Mon
import GMP.Logics.C
import GMP.Logics.P
import GMP.Logics.G
import GMP.Logics.Con
import GMP.Logics.CKCM
import GMP.Logics.SysS
import GMP.Logics.DisjUnion

-- | Runs the parser and the prover and prints the result(s) of obtained.
runLex :: (SigFeature b c d, SigFeature a b (c d), Eq (a (b (c d)))) => Parser (Formula (a (b (c d)))) -> String -> [Bool] -> IO ()
runLex p_rL input flags = run (do spaces
                                  x <- p_rL 
                                  eof
                                  return x
                              ) input flags

run :: (SigFeature b c d, SigFeature a b (c d), Eq (a (b (c d)))) => Parser (Formula (a (b (c d)))) -> String -> [Bool] -> IO ()
run p_r input flags = case (parse p_r "" input) of
                        Left err -> do putStr "parse error at "
                                       print err
                        Right y ->  do let x = preparse y
                        -- show formula that is given to the sequent calculus
                                       putStrLn ("  Current Formula: " ++ pretty x)
                                       putStrLn ("  Trying to show satisfiability...")
                                       let isS = satisfiable x flags
                                       case isS of
                                          True -> putStrLn "  ... The formula is satisfiable"
                                          _    -> putStrLn "  ... The formula is not satisfiable"
                                       putStrLn ("\n  Trying to show provability...")
                                       let isP = provable x flags
                                       case isP of
                                          True -> putStrLn "  ... The formula is provable"
                                          _    -> putStrLn "  ... The formula is not provable"

-- | Parse formula according to the selected modal logic.
runTest :: Int -> String -> [Bool] -> IO ()
runTest ml input flags = do
   case ml of
     1  -> runLex ((parser ((K [])::K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K (K ()))))))))))))))))))))))))))))))))))))))))))) Sqr) ) input flags
     2  -> runLex ((parser ((KD [])::KD (KD (KD (KD (KD (KD (KD (KD (KD (KD (KD (KD (KD (KD ())))))))))))))) Sqr) ) input flags
     3  -> runLex ((parser ((C [1] [])::C (C (C (C (C (C (C (C (C (C (C (C (C (C ())))))))))))))) Sqr) ) input flags
     4  -> runLex ((parser ((G 1 [])::G (G (G (G (G (G (G (G (G (G (G (G (G (G ())))))))))))))) Ang) ) input flags
     5  -> runLex ((parser ((P 1 [])::P (P (P (P (P (P (P (P (P (P (P (P (P (P ())))))))))))))) Ang) ) input flags
     6  -> runLex ((parser ((HM 'a' [])::HM (HM (HM (HM (HM (HM (HM (HM (HM (HM (HM (HM (HM (HM ())))))))))))))) Sqr) ) input flags
     7  -> runLex ((parser ((Mon [])::Mon (Mon (Mon (Mon (Mon (Mon (Mon (Mon (Mon (Mon (Mon (Mon (Mon (Mon ())))))))))))))) Sqr) ) input flags
     8  -> runLex ((parser ((Con [])::Con (Con (Con (Con (Con (Con (Con (Con (Con (Con (Con (Con (Con (Con ())))))))))))))) Sqr) ) input flags
     9  -> runLex ((parser ((SysS [])::SysS (SysS (SysS (SysS (SysS (SysS (SysS (SysS (SysS (SysS (SysS (SysS (SysS (SysS ())))))))))))))) Ang) ) input flags
     10 -> runLex ((parser ((K  [])::K (KD (K (KD (K (KD (K (KD (K (KD (K (KD (K (KD ())))))))))))))) Sqr) ) input flags
     11 -> runLex ((parser ((KD [])::KD (K (KD (K (KD (K (KD (K (KD (K (KD (K (KD (K ())))))))))))))) Sqr) ) input flags
     12 -> runLex ((parser ((Con []):: Con (Mon (K (Con (Mon (K (Con (Mon (K (Con (Mon (K (Con (Mon ())))))))))))))) Sqr) ) input flags
     13 -> runLex ((parser (((DisjUnion ((K [Mod (DisjUnion (K [Mod (DisjUnion (K [Mod (DisjUnion (K [], KD []))], KD [Mod (DisjUnion (K [], KD []))]))], KD [Mod (DisjUnion (K [Mod (DisjUnion (K [], KD []))], KD [Mod (DisjUnion (K [], KD []))]))]))]),(KD [Mod (DisjUnion (K [Mod (DisjUnion (K [Mod (DisjUnion (K [], KD []))], KD [Mod (DisjUnion (K [], KD []))]))], KD [Mod (DisjUnion (K [Mod (DisjUnion (K [], KD []))], KD [Mod (DisjUnion (K [], KD []))]))]))]))))::DisjUnion K KD (DisjUnion K KD (DisjUnion K KD (DisjUnion K KD ( DisjUnion K KD (DisjUnion K KD (DisjUnion K KD (DisjUnion K KD (DisjUnion K KD (DisjUnion K KD (DisjUnion K KD (DisjUnion K KD (DisjUnion K KD (DisjUnion K KD ())))))))))))))) Sqr) ) input flags
     14  -> runLex ((parser ((CKCM [])::CKCM (CKCM (CKCM (CKCM (CKCM (CKCM (CKCM (CKCM (CKCM (CKCM (CKCM (CKCM (CKCM (CKCM ())))))))))))))) Ang) ) input flags
     _ -> showHelp
   return ()

-- | Function for displaying user help 
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
               "         8 for Conditional Modal Logic (CK+CEM)\n" ++
               "         9 for System S (CK+ID+CM+DisjElim)\n" ++
               "        10 for Combined Logic (K KD)\n" ++
               "        11 for Combined Logic (KD K)\n" ++
               "        12 for Combined Logic (Con Mon K)\n" ++
               "        13 for (K + KD)\n" ++
               "        14 for CK+CM\n" ++
               "<path>:  path to input file\n" ++
               "<test>:  test given as a string\n")

-- | main program function
main :: IO()
main = do
    args <- getArgs
    if (args == [])||(head args == "--help")||(length args < 4)
     then showHelp
     else let ml:fl:it:test:[] = take 4 args
          in case it of
               "-p" -> case fl of
                          "-v" -> do input <- readFile test
                                     runTest (read ml) input [True,False]
                          "-o" -> do input <- readFile test
                                     runTest (read ml) input [False,True]
                          _    -> showHelp
               "-t" ->  case fl of
                          "-v" -> runTest (read ml) test [True,False]
                          "-o" -> runTest (read ml) test [False,True]
                          _    -> showHelp
               _    -> showHelp
