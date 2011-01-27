{-# LANGUAGE CPP #-}
{- |
Module      :  $Header$
Description :  cpp choice between "GUI.ProofManagement" and "GUI.GtkProverGUI"
Copyright   :  (c) C. Maeder, Uni Bremen 2002-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (cpp)

cpp choice between "GUI.ProofManagement" and "GUI.GtkProverGUI"
-}

module GUI.ProverGUI
  ( proverGUI ) where

import Logic.Comorphism
import Static.GTheory
import Common.Result as Result
import Proofs.AbstractState
import qualified Comorphisms.KnownProvers as KnownProvers

#ifdef GTKGLADE
import GUI.GtkProverGUI
#elif defined UNI_PACKAGE
import Control.Concurrent
import GUI.HTkProverGUI
#endif

proverGUI :: ProofActions -- ^ record of possible GUI actions
  -> String -- ^ theory name
  -> String -- ^ warning information
  -> G_theory -- ^ theory
  -> KnownProvers.KnownProversMap -- ^ map of known provers
  -> [(G_prover, AnyComorphism)]  -- ^ list of suitable provers and comorphisms
  -> IO (Result.Result G_theory)
#ifdef GTKGLADE
proverGUI = showProverGUI
#elif defined UNI_PACKAGE
proverGUI prGuiAcs thName warningTxt th knownProvers comorphList = do
  guiMVar <- newMVar Nothing
  proofManagementGUI prGuiAcs thName warningTxt th knownProvers comorphList
                     guiMVar
#else
proverGUI = error "not implemented"
#endif
