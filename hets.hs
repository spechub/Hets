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
import Common.Result

import Logic.LogicGraph
import Options
import Static.AnalysisLibrary
import Static.DevGraph
import System.Environment
import ToHaskell.TranslateAna
--import Syntax.Print_HetCASL
--import GUI.ConvertDevToAbstractGraph -- requires uni-package

import ReadFn
import WriteFn
--import ProcessFn

main :: IO ()
main = 
    do opt <- getArgs >>= hetcatsOpts
       putIfVerbose opt 3 ("Options: " ++ show opt)
       sequence_ $ map (processFile opt) (infiles opt)

processFile :: HetcatsOpts -> FilePath -> IO ()
processFile opt file = 
    do putIfVerbose opt 2 ("Processing file: " ++ file)
       ld <- read_LIB_DEFN opt file
       -- (env,ld') <- analyse_LIB_DEFN opt
       (ld',env) <- 
            case (analysis opt) of
                Skip        -> do
                    putIfVerbose opt 2
                        ("Skipping static analysis on file: " ++ file)
                    return (ld, Nothing)
                Structured  -> do
                    putIfVerbose opt 2
                        ("Skipping static analysis on file: " ++ file)
                    return (ld, Nothing)
                Basic       -> do
                    putIfVerbose opt 2 ("Analyzing file: " ++ file)
                    Result diags res <- ioresToIO 
                      (ana_LIB_DEFN logicGraph defaultLogic opt emptyLibEnv ld)
                    sequence (map (putStrLn . show) diags)
                    return (ld, res)
       let odir = if null (outdir opt) then dirname file else outdir opt
       putIfVerbose opt 3 ("Current OutDir: " ++ odir)
       write_LIB_DEFN file (opt { outdir = odir }) ld'
       -- write_GLOBAL_ENV env

