
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
import ATC_sml_cats

-- import ReadFn
-- import WriteFn
-- import ProcessFn

main = do as <- getArgs
	  case as of 
		  [x] -> read_sml_ATerm x >>= print
		  _   -> error "give a filename to read"

m = putStrLn "*** hetcats: Not yet implented"

{-
{-

-}-}