module Main where

import Id
import Token
import Formula
-- import LocalEnv
import Parsec
import ParsecPos
import Pretty
import PrettyPrint
import System
import PrintFormula

main = do {l <- getArgs;
	   if length l < 2 then print 
	   "usage: main {id,term,formula} <filename>"
	   else let option = head l 
	            file = head (tail l)
	   in if option == "id" then checkLines parseId file
	   else if option == "term" then checkLines term file
	   else if option == "formula" then checkLines formula file
--	   else if option == "items" then parseSpec file
	   else print ("unknown option: " ++ option) 
	  }

checkLines p fileName = do { s <- readFile fileName
			   ; putStr (unlines (scanLines p (lines s) 1))
			   }

scanLines _ [] _ = []
scanLines p (x:l) n = (parseLine p x n) : (scanLines p l (n+1))

parseLine p line n = let pos = setSourceLine (initialPos "") n
			 parser = do { setPosition pos
				     ; i <- p
				     ; eof
				     ; return i
				     }
		       in result (parse parser "" line)

{-
parseSpec fileName =  do { r <- parseFromFile basicSpec fileName
			 ; putStrLn (result r)
			 }
	
-}   
result r = case r of Left err -> "parse error at " ++ show err ++ "\n"
		     Right x  -> render (printText0 x) 

