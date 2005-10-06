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
import Common.Result

import Driver.Options

import Comorphisms.LogicGraph

import OWL_DL.OWLAnalysis

import Static.AnalysisLibrary
import Static.DevGraph

import GUI.ShowGraph

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
{-
#ifdef PROGRAMATICA
             HaskellIn -> do
                 r <- anaHaskellFile opts file
                 case gui opts of
                     Not -> return ()
                     _ -> showGraph file opts r
#endif
-}
             OWL_DLIn -> do
                 ontoMap <- parseOWL file
                 paraForGraph <- structureAna file opts ontoMap
                 case gui opts of
                     Not -> return ()
                     _   -> showGraph file opts paraForGraph
             _ -> do
                  Common.Result.Result ds res <- ioresToIO $
                      anaFileOrGetEnv logicGraph opts emptyLibEnv file
                  showDiags opts ds
                  case gui opts of
                      Not -> return ()
                      _  -> showGraph file opts res
