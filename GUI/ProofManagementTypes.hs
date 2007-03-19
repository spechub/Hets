{- |
Module      :  $Header$
Description :  Data type definitions for ProofManagementGUI
Copyright   :  (c) Rene Wagner, Klaus Lüttich, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rainer@tzi.de
Stability   :  provisional
Portability :  needs POSIX

Data type definitions used in GUI.ProofManagement and Proofs.InferBasic.
-}

module GUI.ProofManagementTypes where

import qualified Common.Result as Result

import Proofs.GUIState


-- | Possible actions for GUI which are manipulating ProofGUIState
data ProofGUIActions lid sentence = ProofGUIActions {
    -- | called whenever the "Prove" button is clicked
    proveF :: (ProofGUIState lid sentence
               -> IO (Result.Result (ProofGUIState lid sentence))),
    -- | called whenever the "More fine grained selection" button is clicked
    fineGrainedSelectionF :: (ProofGUIState lid sentence
                          -> IO (Result.Result (ProofGUIState lid sentence))),
    -- | called whenever a (de-)selection occured for updating sublogic
    recalculateSublogicF :: (ProofGUIState lid sentence
                             -> IO (ProofGUIState lid sentence))
  }	  
