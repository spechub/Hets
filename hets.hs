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

{- todo: option for omitting writing of env
         destroy all graphs at the end
-}

module Main where

import Monad (when)

import Common.Utils
import Common.Result
import Common.GlobalAnnotations (emptyGlobalAnnos)
import Syntax.GlobalLibraryAnnotations (initGlobalAnnos)
import Options
import System.Environment
import Events
import Destructible
import Data.IORef

import Comorphisms.LogicGraph
import Logic.Grothendieck
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
             HaskellIn -> do  
	         r <- anaHaskellFile opt file
                 case gui opt of
		     Not -> return ()
                     _ -> showGraph file opt r
             _ -> do
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
				defl <- lookupLogic 
					"logic from command line: " 
					(defLogic opt) logicGraph
                                Common.Result.Result ds res <- ioresToIO 
                                     (ana_LIB_DEFN logicGraph defl opt 
				      emptyLibEnv ld)
                                showDiags opt ds
                                case res of
                                 Just (ln,ld1,_,lenv) -> do
                                   when (EnvOut `elem` outtypes opt)
				        (writeFileInfo opt ds file ln lenv)
				   --checkFile opt file ln lenv
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

checkFile ::  HetcatsOpts -> FilePath -> LIB_NAME -> LibEnv -> IO ()
checkFile opts fp ln lenv =
    case Map.lookup ln lenv of
    Nothing -> putStrLn ("*** Error: Cannot find library "++show ln)
    Just gctx -> do 
      let envFile = rmSuffix fp ++ ".env"
      putStrLn "reading in..."
      (Common.Result.Result dias mread_gctx) <- 
	  globalContextfromShATerm envFile
      maybe (showDiags opts dias)
          (\ read_gctx  -> do
        putStrLn ("read " ++ show (show ln) 
		  ++ " from env-file " ++ show envFile
		  ++ ": status: " 
		  ++ (case read_gctx of
		      (r_globalAnnos, r_globalEnv, r_dGraph) ->
		       case gctx of
		       (globalAnnos, globalEnv, dGraph) ->
		         concat $ 
		          zipWith (\label status ->
				     label ++ ": " ++ status ++ ";")
                             ["GlobalAnnos", " GlobalEnv", " DGraph"]
		             (map (\b -> if b then "ok" else "DIFF!!") 
                                 [r_globalAnnos == globalAnnos,
			          r_globalEnv   == globalEnv,
			          r_dGraph      == dGraph]))))
           mread_gctx
		         
showGraph :: FilePath -> HetcatsOpts -> 
	     Maybe (LIB_NAME, -- filename
                    a,   -- as tree
                    b,   -- development graph
                    LibEnv    -- DGraphs for imported modules 
                   )  -> IO ()
showGraph file opt env =
    case env of
        Just (ln,_,_,libenv) -> do
            putIfVerbose opt 2 ("Trying to display " ++ file
                                ++ "in a graphical Window")
            putIfVerbose opt 3 "Initializing Converter"
            graphMem <- initializeConverter
            putIfVerbose opt 3 "Converting Graph"
            (gid, gv, _cmaps) <- convertGraph graphMem ln libenv
            GUI.AbstractGraphView.redisplay gid gv
            --putIfVerbose opt 1 "Hit CTRL-C when finished"
            (gs,_) <- readIORef gv
            case lookup gid gs of
              Just graph -> sync(destroyed (theGraph graph))
              Nothing -> return ()
            return ()  -- Should destroy all other graphs as well!
        Nothing -> putIfVerbose opt 1
            ("Error: Basic Analysis is neccessary to display "
             ++ "graphs in a graphical window")
