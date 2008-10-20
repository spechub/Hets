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

#ifndef NOOWLLOGIC
import OWL.OWLAnalysis
#endif

#ifdef HXTFILTER
import OMDoc.OMDocInput
#endif

#ifdef UNI_PACKAGE
import GUI.ShowGraph
#endif

#ifdef PROGRAMATICA
import Haskell.Haskell2DG
#endif
import System.Exit (ExitCode(ExitSuccess), exitWith)

#ifdef SHELLAC
import PGIP.Interface
import PGIP.XMLparsing
#endif

main :: IO ()
main = do
    getArgs >>= hetcatsOpts >>= \ opts ->
#ifdef SHELLAC
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
         else
#endif
          do
          putIfVerbose opts 3 ("Options: " ++ show opts)
          mapM_ (processFile opts) (infiles opts)

processFile :: HetcatsOpts -> FilePath -> IO ()
processFile opts file = do
    putIfVerbose opts 3 ("Processing input: " ++ file)
    res <- case guess file (intype opts) of
#ifdef PROGRAMATICA
      HaskellIn -> anaHaskellFile opts file
#endif
#ifndef NOOWLLOGIC
      OWLIn -> do
        ontoMap <- parseOWL file
        structureAna file opts ontoMap
#endif
#ifdef HXTFILTER
      OmdocIn -> mLibEnvFromOMDocFile opts file
#endif
      PrfIn -> anaLibReadPrfs opts file
#ifdef SHELLAC
      ProofCommand -> do
        putStrLn "Start processing a proof command file"
        cmdlProcessFile file
        return Nothing
#endif
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
