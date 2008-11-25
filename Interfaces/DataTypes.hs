{- |
Module      :  $Header$
Description :  Common Data types to be used between interfaces
Copyright   :  (c) Uni Bremen 2002-2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  r.pascanu@gmail.com
Stability   :  provisional
Portability :  non-portable (imports Logic)

Different data structures that are (or should be) shared by all interfaces
of Hets
-}

module Interfaces.DataTypes
       ( IntState(..)
       , IntHistory(..)
       , Int_CmdHistoryDescription(..)
       , IntIState(..)
       , Int_NodeInfo(..)
       , UndoRedoElem(..)
       , ListChange(..)
       ) where


-- import Interface.GenericATPState

import Static.DevGraph
import Common.LibName
import Proofs.AbstractState
import Logic.Comorphism
import Logic.Logic
import Interfaces.GenericATPState


-- | Internal state of the interface, it contains the development graph
-- and a full history. While this in most cases describes the state of
-- development graph at a given time for GUI it is not the same for the
-- PGIP ( it does not describe selected nodes). If one switches from one
-- interface to the other passing this informations should be sufficient
-- with minimal loss of information ( like selected nodes, unfinished
-- script .. and so on)
data IntState = IntState {
   -- global history management
     i_hist  :: IntHistory,
   -- internal state
     i_state :: Maybe IntIState
    }

-- | Contains the detailed global history as two list, a list of actions
-- for undo, and a list of action for redo commands
data IntHistory = IntHistory {
   -- | history for undo command, a list of command descriptions
  undoList :: [Int_CmdHistoryDescription],
  -- | history for redo command, a list of command descriptions
  redoList :: [Int_CmdHistoryDescription]
  }


-- | Contains command description needed for undo/redo actions and
-- for displaying commands in the history
data Int_CmdHistoryDescription = Int_CmdHistoryDescription {
  -- | command name, used for displaying history elements
  cmdName       :: String,
  -- | libname needed to undo actions
  cmdDescription :: [UndoRedoElem]
  }

-- | History elements for the proof state, only LIB_NAME would be used
-- by GUI/ because it keeps track only to changes to the development graph,
-- the other are for PGIP but in order to integrate both they should use
-- same structure
data UndoRedoElem =
   UseThmChange Bool
 | Save2FileChange Bool
 | ProverChange (Maybe G_prover)
 | ConsCheckerChange (Maybe G_cons_checker)
 | ScriptChange ATPTactic_script
 | LoadScriptChange Bool
 | CComorphismChange (Maybe AnyComorphism)
 | ListChange [ListChange]
 | IStateChange (Maybe IntIState)
 | DgCommandChange LIB_NAME

data ListChange =
   AxiomsChange [String] Int
 | GoalsChange [String] Int
 | NodesChange [Int_NodeInfo]


-- | full description of the internal state required by all interfaces
data IntIState = IntIState {
    i_libEnv              :: LibEnv,
    i_ln                  :: LIB_NAME,
    -- these are PGIP specific, but they need to be treated by the common
    -- history mechanism , therefore they need to be here
    elements                 :: [Int_NodeInfo],
    cComorphism           :: Maybe AnyComorphism,
    prover                :: Maybe G_prover,
    consChecker           :: Maybe G_cons_checker,
    save2file             :: Bool,
    useTheorems           :: Bool,
    script                :: ATPTactic_script,
    loadScript            :: Bool
    }


data Int_NodeInfo = forall lid1 sublogics1
         basic_spec1 sentence1 symb_items1 symb_map_items1
         sign1 morphism1 symbol1 raw_symbol1 proof_tree1 .
         Logic lid1 sublogics1 basic_spec1 sentence1
         symb_items1 symb_map_items1 sign1 morphism1
         symbol1 raw_symbol1 proof_tree1 =>
     Element (ProofState lid1 sentence1) Int


