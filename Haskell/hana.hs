{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 
   
test the haskell parser

-}

module Main where

import System.Environment
import Haskell.HatParser
import Haskell.HatAna
import Text.ParserCombinators.Parsec
import Common.GlobalAnnotations

main :: IO ()
main = do
    l <- getArgs
    if length l == 1 
       then do
	    let f = head l
	    r <- parseFromFile hatParser f 
	    putStrLn $ case r of
			 Right decls -> 
                           show $ hatAna (decls, emptySign, emptyGlobalAnnos)
			 Left msg -> show msg
	else do 
	     p <- getProgName
             putStrLn("Usage: "++p++" <file>")

