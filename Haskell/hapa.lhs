#!/home/local-bkb/bin/runhugs

HetCATS/Haskell/hapa.lhs
$Id$
Authors: Christian Maeder
Year:    2003
   
test the haskell parser
needs "-package haskell-src"

\begin{code}

module Main where

import Haskell.Language.Pretty
import Haskell.Language.Parser
import System.Environment

main :: IO ()
main = do
	    s <- getContents
	    let r = parseModuleWithMode (ParseMode "") s
	    putStrLn $ case r of
			 ParseOk x -> prettyPrint x
			 ParseFailed loc msg ->
			     show loc ++ ": " ++ msg
\end{code}
