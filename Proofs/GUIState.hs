{- |
Module      :  $Header$
Description :  State data structure used by the goal management GUI.
Copyright   :  (c) Rene Wagner, Klaus Lüttich, Rainer Grabbe, Uni Bremen 2005-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

The 'ProofGUIState' data structure abstracts the GUI implementation details
away by allowing callback function to use it as the sole input and output.
-}

module Proofs.GUIState where

import qualified Common.OrderedMap as OMap
import qualified Data.Map as Map
import Common.Result as Result
import Common.AS_Annotation
import Common.Utils

import Logic.Logic 
import Logic.Prover
import Logic.Grothendieck

import Comorphisms.KnownProvers

import Static.DevGraph

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
        logicId :: lid,
        -- | sublogic of initial G_theory
        sublogicOfTheory :: G_sublogics,
        -- | last used sublogic to determine fitting comorphisms
        lastSublogic :: G_sublogics,
        -- | goals are stored in a separate map
        goalMap :: ThSens sentence (AnyComorphism,BasicProof),
        -- | currently known provers
        proversMap :: KnownProversMap,
        -- | comorphisms fitting with sublogic of this G_theory
        comorphismsToProvers :: [(G_prover,AnyComorphism)],
        -- | currently selected goals
        selectedGoals :: [String],
        -- | axioms to include for the proof
        includedAxioms :: [String],
        -- | theorems to include for the proof
        includedTheorems :: [String],
        -- | whether a prover is running or not
        proverRunning :: Bool,
        -- | accumulated Diagnosis during Proofs
        accDiags :: [Diagnosis],
        -- | which prover (if any) is currently selected
        selectedProver :: Maybe String,
        -- | Grothendieck theory based upon currently selected goals, axioms
        --   and proven theorems
        selectedTheory :: G_theory
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
             -> [(G_prover,AnyComorphism)]
             -> m (ProofGUIState lid1 sentence1)
initialState lid1 thN th@(G_theory lid2 sig ind thSens _) pm cms = 
    do let (aMap,gMap) = Map.partition (isAxiom . OMap.ele) thSens
           g_th = G_theory lid2 sig ind aMap 0
           sublTh = sublogicOfTh th
       gMap' <- coerceThSens lid2 lid1 "creating initial GUI State" gMap
       return $ 
           ProofGUIState { theoryName = thN,
                           theory = g_th,
                           sublogicOfTheory = sublTh,
                           lastSublogic = sublTh,
                           logicId = lid1,
                           goalMap = gMap',
                           proversMap = pm,
                           comorphismsToProvers = cms,
                           selectedGoals = OMap.keys gMap',
                           includedAxioms = OMap.keys aMap,
                           includedTheorems = OMap.keys gMap,
                           accDiags = [],
                           proverRunning = False,
                           selectedProver =
                               let prvs = Map.keys pm
                               in if null prvs
                                  then Nothing
                                  else 
                                    if defaultGUIProver `elem` prvs
                                       then Just defaultGUIProver
                                       else Nothing
                          ,selectedTheory = g_th
                         }


selectedGoalMap :: ProofGUIState lid sentence
                -> ThSens sentence (AnyComorphism,BasicProof)
selectedGoalMap st = filterMapWithList (selectedGoals st) (goalMap st)

axiomMap :: 
    (Logic  lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                 sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
     Monad m) =>
       ProofGUIState lid1 sentence1 
    -> m (ThSens sentence1 (AnyComorphism,BasicProof))
axiomMap s = 
    case theory s of
    G_theory lid1 _ _ aM _ -> 
        coerceThSens lid1 (logicId s) "Proofs.GUIState.axiomMap" aM
