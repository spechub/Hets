module Main where

import Haskell.Language.Pretty
import Haskell.Language.Syntax
import ToHaskell.TranslateAna
import Common.AnnoState
import Common.Lib.Parsec
import Common.Lib.State
import Common.AnnoState
import Common.GlobalAnnotations
import System.Environment
import HasCASL.Le
import HasCASL.AsToLe(anaBasicSpec)
import HasCASL.ParseItem(basicSpec)


hParser :: AParser HsModule
hParser = do b <- basicSpec
	     return $ translateAna $ snd $ (runState (anaBasicSpec emptyGlobalAnnos b)) initialEnv

	  
main :: IO ()
main = do l <- getArgs
	  if length l >= 1 then
	     do s <- readFile $ head l
		let r = runParser hParser emptyAnnos (head l) s 
	        case r of 
		       --Right x -> putStrLn $ show x
		       Right x -> putStrLn $ prettyPrint x
		       Left err -> putStrLn $ show err
	     else putStrLn "missing argument"
