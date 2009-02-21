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
       , CommandHistory(..)
       , Prove(..)
       , ProvenGoal(..)
       , Command(..)
--       , Node(..)
       , addToHist
       ) where

import Static.DevGraph
import Common.LibName
import Common.Utils(joinWith, splitOn)
import Proofs.AbstractState
import Logic.Comorphism
import Logic.Logic
import Interfaces.GenericATPState
import Data.IORef


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
     i_state :: Maybe IntIState,
   -- file name
     filename :: String
    }

-- | Contains the detailed global history as two list, a list of actions
-- for undo, and a list of action for redo commands
data IntHistory = IntHistory {
  -- | history for undo command, a list of command descriptions
  undoList :: [Int_CmdHistoryDescription],
  -- | history for redo command, a list of command descriptions
  redoList :: [Int_CmdHistoryDescription]
  }

-- | Contains command description needed for undo\/redo actions and
-- for displaying commands in the history
data Int_CmdHistoryDescription = Int_CmdHistoryDescription {
  -- | command name, used for displaying history elements
  cmdName       :: String,
  -- | libname needed to undo actions
  cmdDescription :: [UndoRedoElem]
  }

-- | History elements for the proof state, only LIB_NAME would be used
-- by GUI because it keeps track only to changes to the development graph,
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


data CommandHistory = CommandHistory { hist :: IORef [Command],
                                       filePath :: String}


data Command = ProveCommand Prove deriving Eq

instance Show Command where
    show (ProveCommand p) = show p

data Prove = Prove {nodeNameStr :: String,
                    usedProver  :: Maybe String,
                    translation :: Maybe AnyComorphism,
                    provenGoals :: [ProvenGoal],
                    allAxioms   :: [String]
                    } deriving Eq

instance Show Prove where
   show p =
      "\n# " ++ (replicate 78 '-') ++ "\n\ndg basic " ++ nodeNameStr p ++ "\n\n"
      ++ "drop-translations\n"
      -- selected translation
      ++ (maybe "" (unlines . splitComorphism) $ translation p)
      -- selected prover
      ++ (maybe "# no prover chosen" ("prover "++) $ usedProver p) ++ "\n\n"
      -- proven goals
      ++ (joinWith '\n' $ map (goalToString p) $ provenGoals p)

-- This represents the information about a proved goal
data ProvenGoal = ProvenGoal {name :: String, -- name of the goal
                              axioms :: [String], -- used axioms in the prove
                              time_Limit :: Int -- chosen time-limit
                              } deriving Eq

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
    elements              :: [Int_NodeInfo],
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

goalToString :: Prove -> ProvenGoal -> String
goalToString p g =
    "set goals " ++ (name g)
    ++
    -- axioms to include in prove
    '\n':(if (allAxioms p == axioms g) || (null $ axioms g)
                then "set-all axioms"
                else "set axioms " ++ (joinWith ' ' $ axioms g))
    ++
    -- selected time-limit
    "\nset time-limit " ++ (show $ time_Limit g) ++ "\nprove\n"

-- Splits the comorphism string into its translations.
splitComorphism :: AnyComorphism -> [String]
splitComorphism (Comorphism cid) =
   map ("translate "++) $ tail $ splitOn ';' $ language_name cid

-- Adds a single command to the history.
addToHist :: CommandHistory -> Command -> IO ()
addToHist (CommandHistory {hist = c}) cm =
    readIORef c >>= (\h -> writeIORef c $ h ++ [cm])
