-------------------------------------------------------------------------------
-- GMP
-- Copyright 2007, Lutz Schroeder and Georgel Calin
-------------------------------------------------------------------------------
module Main where 

import Text.ParserCombinators.Parsec
import System.Environment
import IO

import GMPAS
import GMPSAT
import GMPParser
import ModalLogic
import ModalK()
import ModalKD()
import GradedML()
import CoalitionL()
import GenericML()
import Lexer

import qualified Data.Set as Set
-------------------------------------------------------------------------------
-- Funtion to run parser & print
-------------------------------------------------------------------------------
runLex :: (Ord a, Show a, ModalLogic a b) => Parser (Formula a) -> String -> IO ()
runLex p input = run (do
    whiteSpace
    ; x <- p
    ; eof
    ; return x
    ) input

run :: (Ord a, Show a, ModalLogic a b) => Parser (Formula a) -> String -> IO ()
run p input
        = case (parse p "" input) of
                Left err -> do putStr "parse error at "
                               ;print err
                Right x ->  do print "Head of PV list:"
                               let ls = guessPV x ---------------------------
                               let h = if ((not.null) ls) then head(ls)------
                                                          else Set.empty-----
                               print h ------------ FOR TESTING -------------
                               let lro = roFromPV (h) -----------------------
                               print "Rho val from the above PV:"
                               print lro ------------------------------------
                               print "the Formula:"
                               print x
                               print "SAT test answer:"
                               let sat = checksat x
                               print sat

-------------------------------------------------------------------------------
-- For Testing 
-------------------------------------------------------------------------------
runTest :: Int -> FilePath -> IO ()
runTest ml p = do
    input <- readFile (p)
    case ml of
     1 -> runLex ((par5er parseIndex) :: Parser (Formula ModalK)) input
     2 -> runLex ((par5er parseIndex) :: Parser (Formula ModalKD)) input
     3 -> runLex ((par5er parseIndex) :: Parser (Formula CL)) input
     4 -> runLex ((par5er parseIndex) :: Parser (Formula Integer)) input
     _ -> runLex ((par5er parseIndex) :: Parser (Formula Kars)) input
    return ()
help :: IO()
help = do
    putStrLn ( "Usage:\n" ++
               "    ./main <ML> <path>\n\n" ++
               "<ML>:    1 for K ML\n" ++
               "         2 for KD ML\n" ++
               "         3 for Coalition L\n" ++
               "         4 for Graded ML\n" ++
               "         _ for Generic ML\n" ++
               "<path>:  path to input file\n" )
-------------------------------------------------------------------------------
main :: IO()
main = do
    args <- getArgs
    if (args == [])||(head args == "--help")||(length args < 2)
     then help
     else let ml = head args
              p = head (tail args)
          in runTest (read ml) p
