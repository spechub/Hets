module Main where

import Haskell.Hatchet.HsPretty
import Haskell.Hatchet.HsSyn
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

hParser :: AParser [HsDecl]
hParser = do b <- basicSpec
	     return $ translateAna $ snd $ 
		   (runState (anaBasicSpec emptyGlobalAnnos b)) initialEnv
	  
main :: IO ()
main = do l <- getArgs
	  if length l >= 1 then
	     do s <- readFile $ head l
		let r = runParser hParser emptyAnnos (head l) s 
	        case r of 
		       Right hs -> do
		           putStrLn "module HasCASLModul where"
		           putStrLn "import Prelude (undefined)"
			   mapM_ (putStrLn . render . ppHsDecl) hs
		       Left err -> putStrLn $ show err
	     else putStrLn "missing argument"
