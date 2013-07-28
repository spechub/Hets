{-# LANGUAGE CPP #-}
{- |
Module      :  $Id$
Copyright   :  (c) Uni Bremen 2003-2005
License     :  GPLv2 or higher, see LICENSE.txt

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
import Driver.WriteFn

import Static.DevGraph
import Static.FromXml

#ifdef UNI_PACKAGE
import GUI.ShowGraph
import GUI.ShowLogicGraph
#else
import Control.Monad ( when )
#endif

#ifdef PROGRAMATICA
import Haskell.Haskell2DG
#endif

import Common.LibName
import Interfaces.DataTypes
import CMDL.ProcessScript
import CMDL.Interface (cmdlRunShell)
import CMDL.DataTypes
import PGIP.XMLparsing
import PGIP.XMLstate (isRemote)
#ifdef SERVER
import PGIP.Server
#endif

import Maude.Maude2DG (anaMaudeFile)
import LF.Twelf2DG (anaTwelfFile)
import OMDoc.Import (anaOMDocFile)
#ifdef HEXPAT
import HolLight.HolLight2DG (anaHolLightFile)
#endif

#ifdef HAXML
import Isabelle.Isa2DG (anaIsaFile, anaThyFile)
#endif

main :: IO ()
main =
    getArgs >>= hetcatsOpts >>= \ opts ->
#ifdef SERVER
     if serve opts then hetsServer opts else
#endif
     if isRemote opts || (interactive opts && xmlFlag opts)
       then cmdlRun opts >>= displayGraph "" opts . getMaybeLib . intState
       else do
         putIfVerbose opts 3 $ "Options: " ++ show opts
         case infiles opts of
           [] -> displayLogicGraphInfo opts
           fs -> mapM_ (processFile opts) fs

noUniPkg :: IO ()
noUniPkg = fail $ "No graph display interface; \n"
            ++ "UNI_PACKAGE option has been "
            ++ "disabled during compilation of Hets"

displayLogicGraphInfo :: HetcatsOpts -> IO ()
displayLogicGraphInfo opts = case guiType opts of
    NoGui -> writeLG opts
    UseGui ->
#ifdef UNI_PACKAGE
      showPlainLG
#else
      noUniPkg
#endif

processFile :: HetcatsOpts -> FilePath -> IO ()
processFile opts file = do
    putIfVerbose opts 3 ("Processing input: " ++ file)
    let doExit = not $ (guiType opts) /= NoGui || interactive opts
    res <- case guess file (intype opts) of
#ifdef PROGRAMATICA
      HaskellIn -> putStr "this is HaskellIn" >> anaHaskellFile opts file
#endif
#ifdef HEXPAT
      HolLightIn -> anaHolLightFile opts file
#endif
#ifdef HAXML
      IsaIn -> anaIsaFile opts file
      ThyIn -> anaThyFile opts file
#endif
      PrfIn -> anaLibReadPrfs opts file
      ProofCommand -> do
        st <- cmdlProcessFile doExit opts file
        (if (interactive opts) then cmdlRunShell st else return st)
         >>= return . getMaybeLib . intState
      MaudeIn -> anaMaudeFile opts file
      TwelfIn -> anaTwelfFile opts file
      OmdocIn -> anaOMDocFile opts file
      DgXml | not (defLogicIsDMU opts) -> readDGXml opts file
      _ -> anaLib opts file
    case res of
      Just (ln, nEnv) ->
        writeSpecFiles opts file nEnv ln $ lookupDGraph ln nEnv
      _ -> return ()
    displayGraph file opts res

displayGraph :: FilePath -> HetcatsOpts -> Maybe (LibName, LibEnv) -> IO ()
displayGraph file opts res = case guiType opts of
    NoGui -> return ()
    UseGui ->
#ifdef UNI_PACKAGE
      showGraph file opts res
#else
      noUniPkg
#endif
