module Main where

import BasicItem
import LocalEnv
import Parsec
import System

main = do {l <- getArgs;
	   case l of {x:_ -> 
		      do { r <- parseFromFile (basicSpec empty) x;
			   case r of Left err -> do{ putStr "parse error at "
						   ; print err
						   }
		                     Right x  -> print x
			 }; _ -> print "missing argument"
		     }
	  }
	   
