
{- HetCATS/CASL/Main.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   test some parsers (and printers)
-}

module Main where

import Token
import Formula
import Parsec
import ParsecPos
import PrettyPrint
import System
import Print_AS_Basic()
import Parse_AS_Basic
import SortItem
import OpItem
import GlobalAnnotationsFunctions

main :: IO ()
main = do l <- getArgs
	  if length l < 2 then print 
	   "usage: main {id,term,formula,sorts,ops,preds,items} <filename>"
	   else let opt = head l 
	            file = head (tail l)
	   in if opt == "id" then checkLines parseId file
	   else if opt == "term" then checkLines term file
	   else if opt == "formula" then checkLines formula file
	   else if opt == "sorts" then checkLines sortItems file
	   else if opt == "ops" then checkLines opItems file
	   else if opt == "preds" then checkLines predItems file
	   else if opt == "items" then parseSpec file
	   else print ("unknown option: " ++ opt) 

checkLines :: (PrettyPrint a) => GenParser Char () a -> FilePath -> IO ()
checkLines p fileName = do s <- readFile fileName
			   putStr (unlines (scanLines p (lines s) 1))

scanLines :: (Show tok, PrettyPrint a) =>
             GenParser tok () a -> [[tok]] -> Line -> [String]
scanLines _ [] _ = []
scanLines p (x:l) n = (parseLine p x n) : (scanLines p l (n+1))

parseLine :: (Show tok, PrettyPrint a) =>
             GenParser tok () a -> [tok] -> Line -> String
parseLine p line n = let pos = setSourceLine (initialPos "") n
			 parser = do setPosition pos
				     i <- p
				     eof
				     return i
		       in result (parse parser "" line)

parseSpec :: String -> IO ()
parseSpec fileName =  do r <- parseFromFile basicSpec fileName
			 putStrLn (result r)
result :: (Show a, PrettyPrint b) => Either a b -> String
result r = case r of Left err -> "parse error at " ++ show err ++ "\n"
		     Right x  -> renderText (printText0 emptyGlobalAnnos x) 

