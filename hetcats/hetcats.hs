
{- HetCATS/hetcats/hetcats.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   The Main module of the hetcats system. It provides the main function
   to call.

-}

module Main where

import Options
import System
import IO
import ATC_sml_cats
import Print_HetCASL

-- import ReadFn
-- import WriteFn
-- import ProcessFn

main = do as <- getArgs
	  (inp,oup) <- case as of 
		        [inp,oup] -> return (inp,oup)
			_   -> error "give a filename to read and a filename to write"
	  ld <- read_sml_ATerm inp
	  putStrLn $ "In: " ++ inp ++ "\nOut: " ++ oup ++ "\n" ++ show ld
	  putStrLn "Starting to write the output..."
	  hout <- openFile oup WriteMode
	  hPutStr hout $ printLIB_DEFN_text ld

m = putStrLn "*** hetcats: Not yet implented"

