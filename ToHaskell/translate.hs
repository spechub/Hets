module Main where

import HasCASL.ParseItem
import Haskell.Language.Pretty
import Haskell.Language.Syntax
import ToHaskell.Translate
import Common.AnnoState
import Common.Lib.Parsec
import System.Environment

hParser :: AParser HsModule
hParser = do b <- basicSpec
	     return $ translate b
	  
main :: IO ()
main = do l <- getArgs
	  if length l >= 1 then
	     do s <- readFile $ head l
		let r = runParser hParser emptyAnnos (head l) s 
	        case r of 
		       Right x -> putStrLn $ prettyPrint x
		       Left err -> putStrLn $ show err
	     else putStrLn "missing argument"
