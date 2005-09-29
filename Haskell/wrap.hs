{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

test the haskell wrapper

-}

module Main where

import System.Environment
import Haskell.Wrapper
import Text.ParserCombinators.Parsec

main :: IO ()
main = do
    l <- getArgs
    if length l == 1 
       then do
            let f = head l
            s <- readFile f
            let r = parse hStuff f s
            putStr $ case r of
                         Right x -> x
                         Left err -> show err
        else do 
             p <- getProgName
             putStrLn("Usage: "++p++" <file>")
