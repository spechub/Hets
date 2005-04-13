{-# OPTIONS -cpp #-}

{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

   The Main module of the Heterogeneous Tool Set. 
   It provides the main function to call.

-}

{- todo: option for omitting writing of env
-}

module Main where

import Control.Monad (when)

import Common.Utils
import Common.Result
import Common.GlobalAnnotations (emptyGlobalAnnos)
import Syntax.GlobalLibraryAnnotations (initGlobalAnnos)
import Driver.Options
import System.Environment (getArgs)
-- import System.Posix.Process (exitImmediately)
import System.Exit (ExitCode(ExitSuccess), exitWith)

import Comorphisms.LogicGraph
import Logic.Grothendieck
import Static.AnalysisLibrary
import Static.DevGraph
import Static.PrintDevGraph

--import Syntax.Print_HetCASL
#ifdef UNI_PACKAGE
import GUI.AbstractGraphView
import GUI.ConvertDevToAbstractGraph
import InfoBus 
import Events
import Destructible
import DialogWin (useHTk)
#endif

-- for checking the whole ATerm interface
import Syntax.AS_Library (LIB_DEFN(..), LIB_NAME()) 
import qualified Common.Lib.Map as Map

import Driver.ReadFn
import Driver.WriteFn

{-
#ifdef PROGRAMATICA
import Haskell.Haskell2DG
#endif
-}

main :: IO ()
main = 
    do opt <- getArgs >>= hetcatsOpts
       putIfVerbose opt 3 ("Options: " ++ show opt)
       sequence_ $ map (processFile opt) (infiles opt)

processFile :: HetcatsOpts -> FilePath -> IO ()
processFile opt file = 
    do putIfVerbose opt 2 ("Processing file: " ++ file)
       case guess file (intype opt) of
{-
#ifdef PROGRAMATICA
             HaskellIn -> do  
                 r <- anaHaskellFile opt file
                 case gui opt of
                     Not -> return ()
                     _ -> showGraph file opt r
#endif
-}
             _ -> do
                  ld <- read_LIB_DEFN opt file
--                (env,ld') <- analyse_LIB_DEFN opt
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
                                   when (hasEnvOut opt)
                                        (writeFileInfo opt ds file ln lenv)
                                   putIfVerbose opt 5 (showPretty lenv "")
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
                                ++ " in a graphical window")
            putIfVerbose opt 3 "Initializing Converter"
#ifdef UNI_PACKAGE
            graphMem <- initializeConverter
            useHTk -- All messages are displayed in TK dialog windows 
                   -- from this point on
            putIfVerbose opt 3 "Converting Graph"
            (gid, gv, _cmaps) <- convertGraph graphMem ln libenv opt
            GUI.AbstractGraphView.redisplay gid gv
            graph <- get_graphid gid gv
            sync(destroyed graph)
            InfoBus.shutdown
            exitWith ExitSuccess 
#else
            fail "No graph display interface; UNI_PACKAGE option has been disabled during compilation of Hets"
#endif
        Nothing -> putIfVerbose opt 1
            ("Error: Basic Analysis is neccessary to display "
             ++ "graphs in a graphical window")

hasEnvOut :: HetcatsOpts -> Bool
hasEnvOut = any ( \ o -> case o of EnvOut -> True
                                   _ -> False) . outtypes


run  :: FilePath -> IO (Maybe (LIB_NAME, LIB_DEFN, DGraph, LibEnv))
run file = 
    do let opt = defaultHetcatsOpts
       ld <- read_LIB_DEFN opt file
       defl <- lookupLogic "logic from command line: " 
                                        (defLogic opt) logicGraph
       Common.Result.Result ds res <- ioresToIO 
                                       (ana_LIB_DEFN logicGraph defl opt 
                                        emptyLibEnv ld)
       showDiags opt ds
       return res


{- Call this function as follows:
ghci -fglasgow-exts -fno-monomorphism-restriction  -fallow-overlapping-instances -fallow-undecidable-instances -ighc -ifgl -ihxt
:l hets.hs
:module +Common.Lib.Graph
Just (ln,ast,dg,libenv)<-run "../CASL-lib/List.casl"
-}