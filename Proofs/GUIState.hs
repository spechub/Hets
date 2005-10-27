{- |
Module      :  $Header$
Description :  State data structure used by the goal management GUI.
Copyright   :  (c) Rene Wagner, Klaus Lüttich, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  needs POSIX

The 'ProofGUIState' data structure abstracts the GUI implementation details
away by allowing callback function to use it as the sole input and output.

-}

module Proofs.GUIState where

import qualified Common.OrderedMap as OMap
import qualified Common.Lib.Map as Map

import Logic.Logic 
import Logic.Prover
import Logic.Grothendieck

import Comorphisms.KnownProvers

import Static.DevGraph

{- |
  Represents the global state of the prover GUI.
-}
data ProofGUIState lid sentence =  
     ProofGUIState 
      { -- | theory name
        theoryName :: String,
	-- | Grothendieck theory
	theory :: G_theory,
        -- | logic id associated with following maps
        logic_id :: lid,
        -- | axioms are stored in a separate map
        axiomMap :: ThSens sentence (AnyComorphism,BasicProof),
        -- | goals are stored in a separate map
        goalMap :: ThSens sentence (AnyComorphism,BasicProof),
	-- | currently known provers
	proversMap :: KnownProversMap,
        -- | all goals in the theory
        allGoals :: [String],
        -- | currently selected goals
        selectedGoals :: [String],
        -- | whether a prover is running or not
        proverRunning :: Bool,
        -- | wether all goals are selected or not
        allGoalsSelected :: Bool,
        -- | which prover (if any) is currently selected
        selectedProver :: Maybe String
      }

{- |
  Creates an initial State.
-}
initialState :: 
    (Logic  lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                 sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
     Monad m) =>
                lid1
              -> String
             -> G_theory
	     -> KnownProversMap
             -> m (ProofGUIState lid1 sentence1)
initialState lid1 thN th@(G_theory lid2 _ thSens) pm = 
    do thSens' <- coerceThSens lid2 lid1 "creating initial GUI State" thSens
       let (gMap,aMap) = Map.partition (isAxiom . OMap.ele) thSens'
       return $ 
           ProofGUIState { theoryName = thN,
		           theory = th,
                           logic_id = lid1,
                           goalMap = gMap,
                           axiomMap = aMap,
		           proversMap = pm,
                           allGoals = OMap.keys gMap,
                           selectedGoals = [],
                           proverRunning = False,
                           allGoalsSelected = False,
                           selectedProver = if null (Map.keys pm) 
                                            then Nothing
                                            else Just (last $ Map.keys pm)
                         }
      
