{- |
   > HetCATS/hets.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2003

   The Main module of the hetcats system. It provides the main function
   to call.

-}
module Main where

import Common.Utils

import Options
import System.Environment
import Static.AnalysisLibrary
import Logic.LogicGraph
-- import GUI.ConvertDevToAbstractGraph -- requires uni-package

import ReadFn
import WriteFn
-- import ProcessFn
import Syntax.Print_HetCASL

import Debug.Trace

main :: IO ()
main = 
    do opt <- getArgs >>= hetcatsOpts
       if (verbose opt >= 3) then putStr "Options: " >> print opt
          else return ()
       sequence_ $ map (processFile opt) (infiles opt)

processFile :: HetcatsOpts -> FilePath -> IO ()
processFile opt file = 
    do trace ("proceccing file: " ++ file) (return ())
       ld <- read_LIB_DEFN opt file
       -- (env,ld') <- analyse_LIB_DEFN opt
       if (analysis opt)
          then do let odir = if (null (outdir opt)) then (dirname file)
                                else (outdir opt)
                  trace ("selected OutDir: " ++ odir) (return ())
                  write_LIB_DEFN (opt { outdir = odir }) ld
                  -- write_GLOBAL_ENV env
          else putStrLn (take 200 (show (printText0_eGA ld)) ++ "\n...")
{-
  (ast,env) <- 
    if just_parse then return (ld,Nothing)
     else do
       Result diags res <- ioresToIO (ana_LIB_DEFN logicGraph defaultLogic emptyLibEnv ast)
       sequence (map (putStrLn . show) diags)
       return (ast, Just res)
  write_LIB_DEFN opt ast
-}

