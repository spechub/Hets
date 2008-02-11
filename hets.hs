{-# OPTIONS -cpp #-}
{- |
Module      :  $Id$
Copyright   :  (c) Uni Bremen 2003-2005
License     :  Hets is free software; you can redistribute it and/or modify it under the terms of the GNU General Public License as published bythe Free Software Foundation; either version 2 of the License, or (at your option) any later version. Hets comes only with those warranties that are enforced by the applicable law. A copy of the GNU General Public License can be found in LICENSE.TXT.

Maintainer  :  Christian.Maeder@dfki.de
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
import OWL.OWLAnalysis
#endif

import OMDoc.OMDocInput
import Static.AnalysisLibrary

#ifdef UNI_PACKAGE
import GUI.ShowGraph
#endif

#ifdef PROGRAMATICA
import Haskell.Haskell2DG
#endif
import System.Exit (ExitCode(ExitSuccess), exitWith)

import PGIP.Interface
import PGIP.XMLparsing
main :: IO ()
main = do
    opts <- getArgs >>= hetcatsOpts
    if (port opts /= -1)
     then do
      cmdlConnect2Port $ port opts
      return ()
     else do
      if (interactive opts)
       then do
        if (xml opts)
         then do
          cmdlRunXMLShell
          return ()
         else do
          cmdlRunShell (infiles opts)
          return ()
       else do
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
                          OWLIn -> do
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
                          ProofCommand -> do
                               putStrLn "Start processing a proof command file"
                               cmdlProcessFile file
                               return Nothing
                          _ -> anaLib opts file
                        case gui opts of
                           Not -> return ()
                           _  -> do
#ifdef UNI_PACKAGE
                              showGraph file opts res
                              exitWith ExitSuccess
#else
                              fail $ "No graph display interface; \n" ++
                                     "UNI_PACKAGE option has been "++
                                     "disabled during compilation of Hets"
#endif
