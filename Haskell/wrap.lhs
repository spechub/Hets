#!/home/local-bkb/bin/runhugs

HetCATS/Haskell/wrap.lhs
$Id$
Authors: Christian Maeder
Year:    2003
   
test the haskell parser
needs "-package haskell-src"

\begin{code}

module Main where

import System.Environment
import Wrapper
import Common.Lib.Parsec

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

\end{code}
