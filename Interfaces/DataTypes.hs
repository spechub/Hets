{-# LANGUAGE ExistentialQuantification #-}
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
  ( IntState (..)
  , getMaybeLib
  , IntHistory (..)
  , CmdHistory (..)
  , IntIState (..)
  , Int_NodeInfo (..)
  , UndoRedoElem (..)
  , ListChange (..)
  ) where

import Static.DevGraph
import Common.LibName
import Proofs.AbstractState
import Logic.Comorphism
import Logic.Logic
import Interfaces.Command
import Interfaces.GenericATPState

-- | Internal state of the interface, it contains the development graph
-- and a full history. While this in most cases describes the state of
-- development graph at a given time for GUI it is not the same for the
-- PGIP ( it does not describe selected nodes). If one switches from one
-- interface to the other passing this informations should be sufficient
-- with minimal loss of information ( like selected nodes, unfinished
-- script .. and so on)
data IntState = IntState
  { i_hist  :: IntHistory -- ^ global history management
  , i_state :: Maybe IntIState -- ^ internal state
  , filename :: String }

getMaybeLib :: IntState -> Maybe (LibName, LibEnv)
getMaybeLib = fmap (\ s -> (i_ln s, i_libEnv s)) . i_state

-- | Contains the detailed global history as two list, a list of actions
-- for undo, and a list of action for redo commands
data IntHistory = IntHistory
  { undoList :: [CmdHistory]
  , redoList :: [CmdHistory] }

-- | Contains command description needed for undo\/redo actions and
-- for displaying commands in the history
data CmdHistory = CmdHistory
  { command :: Command
  , cmdHistory :: [UndoRedoElem] }

-- | History elements for the proof state, only LibName would be used
-- by GUI because it keeps track only to changes to the development graph,
-- the other are for PGIP but in order to integrate both they should use
-- same structure
data UndoRedoElem =
    UseThmChange Bool
  | Save2FileChange Bool
  | ProverChange (Maybe G_prover)
  | ConsCheckerChange (Maybe G_cons_checker)
  | ScriptChange ATPTacticScript
  | LoadScriptChange Bool
  | CComorphismChange (Maybe AnyComorphism)
  | ListChange [ListChange]
  | IStateChange (Maybe IntIState)
  | DgCommandChange LibName

data ListChange =
    AxiomsChange [String] Int
  | GoalsChange [String] Int
  | NodesChange [Int_NodeInfo]

-- | full description of the internal state required by all interfaces
data IntIState = IntIState
  { i_libEnv :: LibEnv
  , i_ln :: LibName
  -- these are PGIP specific, but they need to be treated by the common
  -- history mechanism , therefore they need to be here
  , elements :: [Int_NodeInfo]
  , cComorphism :: Maybe AnyComorphism
  , prover :: Maybe G_prover
  , consChecker :: Maybe G_cons_checker
  , save2file :: Bool
  , useTheorems :: Bool
  , script :: ATPTacticScript
  , loadScript :: Bool }

data Int_NodeInfo = forall lid1 sublogics1
         basic_spec1 sentence1 symb_items1 symb_map_items1
         sign1 morphism1 symbol1 raw_symbol1 proof_tree1 .
         Logic lid1 sublogics1 basic_spec1 sentence1
         symb_items1 symb_map_items1 sign1 morphism1
         symbol1 raw_symbol1 proof_tree1 =>
     Element (ProofState lid1 sentence1) Int

