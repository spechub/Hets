{-# LANGUAGE CPP #-}

module Driver.ReadMain where


import Control.Monad

import Common.LibName

import Interfaces.DataTypes


import CMDL.ProcessScript
import CMDL.Interface (cmdlRunShell)
import CMDL.DataTypes

import Driver.AnaLib
import Driver.Options

import Static.DevGraph


import Maude.Maude2DG (anaMaudeFile)
import LF.Twelf2DG (anaTwelfFile)
import OMDoc.Import (anaOMDocFile)
#ifdef HEXPAT
import HolLight.HolLight2DG (anaHolLightFile)
#endif

#ifdef HAXML
import Isabelle.Isa2DG (anaIsaFile, anaThyFile)
#endif

readAndAnalyse :: FilePath -> HetcatsOpts -> IO (Maybe (LibName, LibEnv))
readAndAnalyse file opts = 
    let doExit = guiType opts == UseGui in case guess file (intype opts) of
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
        liftM (getMaybeLib . intState)
          $ (if interactive opts then cmdlRunShell else return) st
      MaudeIn -> anaMaudeFile opts file
      TwelfIn -> anaTwelfFile opts file
      OmdocIn -> anaOMDocFile opts file
      _ -> anaLib opts file