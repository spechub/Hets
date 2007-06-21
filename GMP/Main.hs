-- this has to be modified
-------------------------------------------------------------------------------
-- GMP
-- Copyright 2007, Lutz Schroeder and Georgel Calin
-------------------------------------------------------------------------------
module Main where 

import Text.ParserCombinators.Parsec
import System.Environment
import IO

import GMPAS
import GMPParser
import ModalLogic()
import ModalK()
import ModalKD()
import GradedML()
import CoalitionL()
import GenericML()

runTest :: Int -> FilePath -> IO ()
runTest ml p = do
    input <- readFile (p)
    case ml of
     1 -> runLex (par5er :: Parser (Formula ModalK)) input
     2 -> runLex (par5er :: Parser (Formula ModalKD)) input
     3 -> runLex (par5er :: Parser (Formula CL)) input
     4 -> runLex (par5er :: Parser (Formula Integer)) input
     _ -> runLex (par5er :: Parser (Formula Kars)) input
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
main :: IO()
main = do
    args <- getArgs
    if (args == [])||(head args == "--help")||(length args < 2)
     then help
     else let ml = head args
              p = head (tail args)
          in runTest (read ml) p
