module Main where

import Lexer
import BasicItem
import LocalEnv
import Parsec
import ParsecPos
import System

main = do {l <- getArgs;
	   if null l then print "missing argument"
--	   else parseSpec (head l)
           else checkIds (head l)
	  }


checkIds fileName = do { s <- readFile fileName
                       ; putStr (unlines (scanLines (lines s) 1))
		       }

scanLines [] _ = []
scanLines (x:l) n = (scanId x n) : (scanLines l (n+1))

scanId line n = let pos = setSourceLine (initialPos "") n
		    parser = do { setPosition pos
				; i <- parseId
				; eof
				; return i
				}
		in result (parse parser "" line)


parseSpec fileName =  do { r <- parseFromFile (basicSpec empty) fileName
			 ; putStrLn (result r)
			 }
	   
result r = case r of Left err -> "parse error at " ++ show err ++ "\n"
		     Right x  -> show x

