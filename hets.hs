{- |
   > HetCATS/hets.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2003

   The Main module of the hetcats system. It provides the main function
   to call.

-}
module Main where

import Options
import System.Environment

import ReadFn
import WriteFn
-- import ProcessFn

main :: IO ()
main = do opt <- getArgs >>= hetcatsOpts
	  if (verbose opt >= 3) then putStr "Options: " >> print opt
	   else return ()
	  ld <- read_LIB_DEFN opt
	  -- (env,ld') <- analyse_LIB_DEFN opt
	  write_LIB_DEFN opt ld
	  -- write_GLOBAL_ENV env

