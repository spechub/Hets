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
import Haskell.Hatchet.HsParseMonad
import Haskell.Hatchet.HsParser
import Haskell.Hatchet.HsSyn
import Haskell.Hatchet.HsPretty
import Haskell.HatAna
import Haskell.Hatchet.MultiModuleBasics

main :: IO ()
main = do
    l <- getArgs
    if length l == 1 
       then do
	    let f = head l
	    s <- readFile f
	    let r = parse s (SrcLoc 1 0) 0 []
	    putStrLn $ case r of
			 Ok _ (HsModule _ _ _ decls) -> 
                           show (hatAna decls emptyModuleInfo)
			 Failed msg -> msg
-- OK and Failed are constructors of HsParseMonad.ParseResult
	else do 
	     p <- getProgName
             putStrLn("Usage: "++p++" <file>")

