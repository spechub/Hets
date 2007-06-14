----------------------------------------------------------------
-- GMP
-- Copyright 2007, Lutz Schroeder and Georgel Calin
----------------------------------------------------------------
module Main where 

-- import Text.ParserCombinators.Parsec
import IO

-- import GMPAS
import GMPParser

askForInput = do
    putStrLn ("Please enter the name of the test file (or \"\" to stop):")
    name <- getLine
    if name == "" 
        then return []
        else do
            input <- readFile name
            runLex par5er input
            askForInput
            return []
main = do
    hSetBuffering stdin LineBuffering
    askForInput
{-
    putStrLn "Give the name of the test file: "
    name <- getLine
    input <- readFile name
    runLex par5er input
-}
