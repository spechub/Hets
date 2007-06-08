----------------------------------------------------------------
-- GMP
-- Copyright 2007, Lutz Schroeder and Georgel Calin
----------------------------------------------------------------
module Main where 

import Text.ParserCombinators.Parsec
import IO

import GMPAS
import GMPParser

test input 
	= do result <- parseFromFile program name
		;case result of
			Left err -> do putStr "parse error at: " ;print err
			Right x  -> print x
main = do
    hSetBuffering stdin LineBuffering
    putStrLn "Give the name of the test file: "
    name <- getLine
    test name
