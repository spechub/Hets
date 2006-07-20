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
import Driver.ReadFn

#ifdef CASLEXTENSIONS
import OWL_DL.OWLAnalysis
#endif

import OMDoc.OMDocInput
import Static.AnalysisLibrary

#ifdef UNI_PACKAGE
import GUI.ShowGraph
#endif

#ifdef PROGRAMATICA
import Haskell.Haskell2DG
#endif

import PGIP.Command_Parser

main :: IO ()
main = do
    opts <- getArgs >>= hetcatsOpts
    putIfVerbose opts 3 ("Options: " ++ show opts)
    mapM_ (processFile opts) (infiles opts)

processFile :: HetcatsOpts -> FilePath -> IO ()
processFile opts file =
    do putIfVerbose opts 3 ("Processing input: " ++ file)
       case guess file (intype opts) of
         s -> do
           res <- case s of

#ifdef PROGRAMATICA
             HaskellIn -> anaHaskellFile opts file
#endif

#ifdef CASLEXTENSIONS
             OWL_DLIn -> do
                 ontoMap <- parseOWL file
                 structureAna file opts ontoMap
#endif
             OmdocIn -> do
               mLibEnvFromOMDocFile opts file
             PrfIn -> do
               m <- anaLib (removePrfOut opts) file
               case m of
                 Nothing -> return Nothing
                 Just (ln, libEnv) -> do
                     proofStatus <- readPrfFiles opts libEnv
                     return $ Just (ln, proofStatus)
             ProofCommand -> parseScriptFile file
             _ -> anaLib opts file
           case gui opts of
             Not -> return ()
             _  ->
#ifdef UNI_PACKAGE
                   showGraph file opts res
#else
                   fail $ "No graph display interface; \n" ++
                          "UNI_PACKAGE option has been "++
                          "disabled during compilation of Hets"
#endif
