module Main where

import OWL_DL.ReadWrite
import Common.ATerm.Lib
import System

main :: IO()
main =
    do filename <- getArgs 
       str <- readFile $ head filename  
       let atermTable = readATerm str
       putStrLn $ show $ getATermFull atermTable
