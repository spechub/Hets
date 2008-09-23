{-# OPTIONS -cpp #-}
{- |
Module      :  $Id$
Copyright   :  (c) Uni Bremen 2003-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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
import Driver.AnaLib

#ifdef CASLEXTENSIONS
import OWL.OWLAnalysis
#endif

import OMDoc.OMDocInput

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
    if connectP opts /= -1
     then
      cmdlConnect2Port (xmlFlag opts) (connectH opts) (connectP opts)
      >> return ()
     else
      if listen opts /= -1
       then
        cmdlListen2Port (xmlFlag opts) (listen opts) >> return ()
       else
        if interactive opts
         then do
          if xmlFlag opts
           then
            cmdlRunXMLShell
           else
            cmdlRunShell (infiles opts)
          return ()
         else do
          putIfVerbose opts 3 ("Options: " ++ show opts)
          mapM_ (processFile opts) (infiles opts)

processFile :: HetcatsOpts -> FilePath -> IO ()
processFile opts file = do
    putIfVerbose opts 3 ("Processing input: " ++ file)
    res <- case guess file (intype opts) of
#ifdef PROGRAMATICA
      HaskellIn -> anaHaskellFile opts file
#endif
#ifdef CASLEXTENSIONS
      OWLIn -> do
        ontoMap <- parseOWL file
        structureAna file opts ontoMap
#endif
      OmdocIn -> mLibEnvFromOMDocFile opts file
      PrfIn -> anaLibReadPrfs opts file
      ProofCommand -> do
        putStrLn "Start processing a proof command file"
        cmdlProcessFile file
        return Nothing
      _ -> anaLib opts file
    case guiType opts of
      NoGui -> return ()
      UseGui -> do
#ifdef UNI_PACKAGE
        showGraph file opts res
        exitWith ExitSuccess
#else
        fail $ "No graph display interface; \n"
          ++ "UNI_PACKAGE option has been "
          ++ "disabled during compilation of Hets"
#endif
