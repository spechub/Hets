module Main where

import ParseItem
import ParseTerm
import PrintAs
import HToken
import Parsec
import ParsecPos
import Pretty
import PrettyPrint
import System

main = do {l <- getArgs;
	   if length l < 2 then print 
	   "usage: main <opt> <filename>"
	   else let opt = head l 
	            file = head (tail l)
	   in if opt == "id" then checkLines uninstOpName file
	   else if opt == "typename" then checkLines typeName file
	   else if opt == "type" then checkLines parseType file
	   else if opt == "term" then checkLines term file
	   else if opt == "typepattern" then checkLines typePattern file
	   else if opt == "pattern" then checkLines pattern file
	   else if opt == "item" then checkLines basicSpec file
	   else if opt == "items" then parseSpec file
	   else print ("unknown option: " ++ opt) 
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


parseSpec fileName =  do { r <- parseFromFile basicSpec fileName
			 ; putStrLn (result r)
			 }
   
result r = case r of Left err -> "parse error at " ++ show err ++ "\n"
		     Right x  -> renderText (printText0 x)

