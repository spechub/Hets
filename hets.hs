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
import Static.AnalysisLibrary
import Logic.LogicGraph
-- import GUI.ConvertDevToAbstractGraph -- requires uni-package

import ReadFn
import WriteFn
-- import ProcessFn

main :: IO ()
main = do 
  opt <- getArgs >>= hetcatsOpts
  if (verbose opt >= 3) then putStr "Options: " >> print opt
    else return ()
  ld <- read_LIB_DEFN opt
  write_LIB_DEFN opt ld
{-
  (ast,env) <- 
    if just_parse then return (ld,Nothing)
     else do
       Result diags res <- ioresToIO (ana_LIB_DEFN logicGraph defaultLogic emptyLibEnv ast)
       sequence (map (putStrLn . show) diags)
       return (ast, Just res)
  write_LIB_DEFN opt ast
	  -- write_GLOBAL_ENV env


-}
