{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2003-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The Main module of the Heterogeneous Tool Set.
   It provides the main function to call (and not much more).

-}

-- for interactice purposes use Test.hs

module Main where

import System.Environment (getArgs)

import Driver.Options

#ifdef CASLEXTENSIONS
import OWL_DL.OWLAnalysis
#endif

import Static.AnalysisLibrary

#ifdef UNI_PACKAGE
import GUI.ShowGraph
#endif

{-
#ifdef PROGRAMATICA
import Haskell.Haskell2DG
#endif
-}

main :: IO ()
main = do
    opts <- getArgs >>= hetcatsOpts
    putIfVerbose opts 3 ("Options: " ++ show opts)
    mapM_ (processFile opts) (infiles opts)

processFile :: HetcatsOpts -> FilePath -> IO ()
processFile opts file =
    do putIfVerbose opts 2 ("Processing input: " ++ file)
       case guess file (intype opts) of
#ifdef UNI_PACKAGE
         DGIn -> showDGGraph file opts
#endif
         s -> do 
           res <- case s of
{-
#ifdef PROGRAMATICA
             HaskellIn -> anaHaskellFile opts file
#endif
-}
#ifdef CASLEXTENSIONS
             OWL_DLIn -> do
                 ontoMap <- parseOWL file
                 structureAna file opts ontoMap
#endif
             _ -> anaLib opts file
           case gui opts of
             Not -> return ()
#ifdef UNI_PACKAGE
             _  -> showGraph file opts res
#endif
