#!/home/local-bkb/bin/runhugs

HetCATS/Haskell/hapa.lhs
$Id$
Authors: Christian Maeder
Year:    2003
   
test the haskell parser
needs "-package haskell-src"

\begin{code}

module Main where

import Language.Haskell.Pretty
import Language.Haskell.Parser
import System.Environment

main :: IO ()
main = do
    l <- getArgs
    if length l == 1 
       then do
	    let f = head l
	    s <- readFile f
	    let r = parseModuleWithMode (ParseMode f) s
	    putStrLn $ case r of
			 ParseOk x -> prettyPrint x
			 ParseFailed loc msg ->
			     show loc ++ ": " ++ msg
	else do 
	     p <- getProgName
             putStrLn("Usage: "++p++" <file>")

\end{code}
