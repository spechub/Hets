{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

   The Main module of the hetcats system. It provides the main function
   to call.

-}
module Main where

import Monad (when)

import Common.Utils
import Common.Result
import Common.GlobalAnnotations (emptyGlobalAnnos)
import Syntax.GlobalLibraryAnnotations (initGlobalAnnos)
import Options
import System.Environment

import Comorphisms.LogicGraph
import Static.AnalysisLibrary
import Static.DevGraph

--import Syntax.Print_HetCASL
import GUI.AbstractGraphView
import GUI.ConvertDevToAbstractGraph

-- for checking the whole ATerm interface
import Syntax.AS_Library (LIB_DEFN(..), LIB_NAME()) 
import qualified Common.Lib.Map as Map

import ReadFn
import WriteFn
--import ProcessFn

import Haskell.Haskell2DG

main :: IO ()
main = 
    do opt <- getArgs >>= hetcatsOpts
       putIfVerbose opt 3 ("Options: " ++ show opt)
       sequence_ $ map (processFile opt) (infiles opt)

processFile :: HetcatsOpts -> FilePath -> IO ()
processFile opt file = 
    do putIfVerbose opt 2 ("Processing file: " ++ file)
       case guess file (intype opt) of
             HaskellIn -> do  r <- anaHaskellFile opt file
                              showGraph file opt r
             _         -> 
                do
                  ld <- read_LIB_DEFN opt file
               -- (env,ld') <- analyse_LIB_DEFN opt
                  (ld'@(Lib_defn libname _ _ _),env) <- 
                     case (analysis opt) of
                             Skip        -> do
                                putIfVerbose opt 2
                                    ("Skipping static analysis on file: " ++ file)
                                return (ld, Nothing)
                             _       -> do
                                putIfVerbose opt 2 ("Analyzing file: " ++ file)
                                Common.Result.Result diags res <- ioresToIO 
                                     (ana_LIB_DEFN logicGraph defaultLogic opt emptyLibEnv ld)
                                showDiags opt diags
                                case res of
                                     Just (ln,ld1,_,lenv) -> do
                                       writeFileInfo opt file ln lenv
				       --checkFile file ln lenv
                                       return (ld1,res)
                                     Nothing -> return (ld, res)
                  let odir = if null (outdir opt) then dirname file else outdir opt
                  putIfVerbose opt 3 ("Current OutDir: " ++ odir)
		  let (globalAnnos,notTrans) = 
			  maybe (maybe emptyGlobalAnnos
				       id
				       ((\ (Common.Result.Result _ m) -> m) 
					  (initGlobalAnnos ld')),True)
			        (\ (_,_,_,libEnv) ->
			           maybe (error ("Library "
					     ++ show libname
					     ++ " not found after analysis"))
				         (\ (ga,_,_) -> (ga,False))
				         (Map.lookup libname libEnv))
			        env
		  when notTrans (putIfVerbose opt 2 
				  ("Warning: Printing without "
				   ++"transitive imported Global Annotations"))
                  case gui opt of
                      Only    -> showGraph file opt env
                      Also    -> do showGraph file opt env
                                    write_LIB_DEFN globalAnnos 
						   file 
						   (opt { outdir = odir }) 
						   ld'
                                    -- write_GLOBAL_ENV env
                      Not     -> write_LIB_DEFN globalAnnos 
				                file 
						(opt { outdir = odir }) 
						ld'

checkFile :: FilePath -> LIB_NAME -> LibEnv -> IO ()
checkFile fp ln lenv =
    case Map.lookup ln lenv of
    Nothing -> putStrLn ("*** Error: Cannot find library "++show ln)
    Just gctx -> do 
      let envFile = rmSuffix fp ++ ".env"
      read_gctx <- globalContextfromShATerm envFile
      putStrLn ("read " ++ show (show ln) 
		++ " from env-file " ++ show envFile
		++ ": status: " 
		++ (if read_gctx == gctx 
		    then "no differences found"
		    else "INCONSISTENT environments!!"))



{- showGraph :: FilePath -> HetcatsOpts -> (Maybe (LIB_NAME, -- filename
                                                      HsModule, -- as tree
                                                      DGraph,   -- development graph
                                                      LibEnv    -- DGraphs for imported modules 
                                                      )  -> IO ()
-}
showGraph file opt env =
    case env of
        Just (ln,_,_,libenv) -> do
            putIfVerbose opt 2 ("Trying to display " ++ file
                                ++ "in a graphical Window")
            putIfVerbose opt 3 "Initializing Converter"
            graphMem <- initializeConverter
            putIfVerbose opt 3 "Converting Graph"
            (gid, gv, cmaps) <- convertGraph graphMem ln libenv
            GUI.AbstractGraphView.redisplay gid gv
            putIfVerbose opt 1 "Hit Return when finished"
            getLine
            return ()
        Nothing -> putIfVerbose opt 1
            ("Error: Basic Analysis is neccessary to display "
             ++ "graphs in a graphical window")
