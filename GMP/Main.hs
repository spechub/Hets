----------------------------------------------------------------
-- GMP
-- Copyright 2007, Lutz Schroeder and Georgel Calin
----------------------------------------------------------------
module Main where 

import Text.ParserCombinators.Parsec
import IO

import GMPAS
import GMPParser
import ModalLogic
import ModalK
import ModalKD
import ModalInt
import ModalBS
import ModalKar

askForInput = do
    option <- getLine
    putStrLn ("Please enter the name of the test file (or \"\" to stop):")
    name <- getLine
    if name == "" 
     then return ()
     else do
      input <- readFile ("./tests/" ++ name)
      if read option == 1 
       then runLex (par5er :: Parser (Formula Integer)) input
       else if read option == 2
        then runLex (par5er :: Parser (Formula BitString)) input
        else if read option == 3
         then runLex (par5er :: Parser (Formula ModalK)) input
         else if read option == 4
          then runLex (par5er :: Parser (Formula ModalKD)) input
          else runLex (par5er :: Parser (Formula Kars)) input
      askForInput
      return ()
main = do
    hSetBuffering stdin LineBuffering
    putStrLn ("Please enter \n" ++
             "    1 for integer index\n" ++
             "    2 for bit-string index\n" ++
             "    3 for K () index\n" ++
             "    4 for KD () index\n" ++
             "    another digit for string indexes")
    askForInput
