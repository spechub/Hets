{- |
Module      :  $Header$
Description :  State data structure used by the goal management GUI.
Copyright   :  (c) Rene Wagner, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rwagner@tzi.de
Stability   :  provisional
Portability :  needs POSIX

The 'ProofGUIState' data structure abstracts the GUI implementation details
away by allowing callback function to use it as the sole input and output.

-}

module Proofs.GUIState where

{- |
  Represents the global state of the prover GUI.
-}
data ProofGUIState = ProofGUIState { -- | currently selected goal or Nothing
                                     selectedGoals :: [String],
                                     -- | whether a prover is running or not
                                     proverRunning :: Bool,
                                     -- | which prover (if any) is currently selected
                                     selectedProver :: Maybe String
                                   }

{- |
  Creates an initial State.
-}
initialState :: ProofGUIState
initialState = 
  ProofGUIState { selectedGoals = [],
                  proverRunning = False,
                  selectedProver = Nothing
                }

