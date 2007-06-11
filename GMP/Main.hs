----------------------------------------------------------------
-- GMP
-- Copyright 2007, Lutz Schroeder and Georgel Calin
----------------------------------------------------------------
module Main where 

import Text.ParserCombinators.Parsec
import IO

import GMPAS
import GMPParser

main = do
    hSetBuffering stdin LineBuffering
    putStrLn "Give the name of the test file: "
    name <- getLine
    input <- readFile name
    runLex par5er input
