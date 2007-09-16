{- |
Module      :$Header$
Description : Internal state of the CMDL interface
Copyright   : uni-bremen and DFKI
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.CMDLState describes the internal state of the CMDL 
interface and provides basic functions related to the 
internal state.
-} 


module PGIP.CMDLState
       ( CMDLProofAbstractState(..)
       , initCMDLProofAbstractState
       , CMDLProveState(..)
       , CMDLDevGraphState(..)
       , CMDLState(..)
       , UndoRedoElem(..)
       , ProofStatusChange(..)
       , GoalAxm(..)
       , emptyCMDLState
       , getAllNodes
       , getAllGoalNodes
       , getAllEdges
       , getAllGoalEdges
       , CommandTypes(..)
       , ActionType(..)
       , obtainGoalNodeList
       , getTh
       ) where 

import PGIP.CMDLUtils

import Common.Result

import Data.List
import Data.Graph.Inductive.Graph

import Static.GTheory
import Static.DevGraph
import Static.DGToSpec

import Logic.Grothendieck
import Logic.Logic

import Syntax.AS_Library

import Proofs.AbstractState

-- AbstractState depends on lid and sentence, and in order
-- not to change to much CMDLProveState requires some 
-- independent type
-- also CMDL interface requires to keep track of the node
-- number
data CMDLProofAbstractState = forall lid1 sublogics1 
         basic_spec1 sentence1 symb_items1 symb_map_items1
         sign1 morphism1 symbol1 raw_symbol1 proof_tree1 .
         Logic lid1 sublogics1 basic_spec1 sentence1 
         symb_items1 symb_map_items1 sign1 morphism1 
         symbol1 raw_symbol1 proof_tree1 =>
     Element (ProofState lid1 sentence1) Int


-- | Constructor for CMDLProofGUIState datatype
initCMDLProofAbstractState:: (Logic lid1 sublogics1
         basic_spec1 sentence1 symb_items1 symb_map_items1 
         sign1 morphism1 symbol1 raw_symbol1 proof_tree1) =>
         ProofState lid1 sentence1 -> Int 
         -> CMDLProofAbstractState
initCMDLProofAbstractState ps nb
 = Element ps nb

data ProofStatusChange =
   AxiomsChange [String] Int
 | GoalsChange [String] Int

-- | Each time is stored the data that used to be
data UndoRedoElem =
   UseThmChange Bool
 | Save2FileChange Bool
 | ProverChange (Maybe G_prover)
 | ScriptChange String
 | LoadScriptChange Bool
 | CComorphismChange (Maybe AnyComorphism)
 | ListChange [ProofStatusChange]
 | ProveChange LibEnv [ProofStatusChange]


-- | During the prove mode, the CMDL interface will use the 
-- informations stored in the Prove state, which consists of 
-- the list of elements selected,  the list of comorphism 
-- applied to the list (where the first in the list is the 
-- last applied comorphism, the selected prover and the 
-- script.
data CMDLProveState = 
  CMDLProveState {
    -- | selected nodes as elements (only the theory and the
    -- node number from where the theory was taken)
    elements     :: [CMDLProofAbstractState] ,
    -- | composed comorphism resulting from all the selected
    -- comorphisms. 
    cComorphism :: Maybe AnyComorphism,
    -- | Selected prover
    prover      :: Maybe G_prover,
    -- | Save for each goal the output from the prover in a file
    save2file   :: Bool,
    -- | Use proven theorems in subsequent proofs
    useTheorems :: Bool,
    -- | Script to be used when proving
    script      :: String,
    -- | If script is currently being inserted
    loadScript  :: Bool,
    -- | History elements
    historyList :: ([UndoRedoElem], [UndoRedoElem])
    }


-- | During the development graph mode, the CMDL interface 
-- will use the information stored in CMDLDevGraphState which 
-- consist of the library loaded and a list of all nodes 
-- and edges.
data CMDLDevGraphState = CMDLDevGraphState {
    -- | the LIB_NAME of the loaded library
    ln               :: LIB_NAME,
    -- | the LibEnv of the loaded library
    libEnv           :: LibEnv,
    -- | List of all nodes from the development graph. 
    -- List might be out of date, please use 
    -- allNodesUpToDate to check
    allNodes         :: [LNode DGNodeLab],
    -- | Indicator if the list of all nodes is up to date 
    -- or if it needs 
    -- to be recomputed
    allNodesUpToDate :: Bool,
    -- | List of all edges from the development graph. List 
    -- might be out of date, please use allEdgesUpToDate to 
    -- check
    allEdges         :: [LEdge DGLinkLab],
    -- | Indicator if the list of all edges is up to date or 
    -- if it needs to be recomputed
    allEdgesUpToDate :: Bool
    }

 
-- | CMDLState contains all information the CMDL interface
-- might use at any time.
data CMDLState = CMDLState {
  -- | development  graph mode information
  devGraphState   :: Maybe CMDLDevGraphState,
  -- | prove mode information
  proveState      :: Maybe CMDLProveState,
  -- | promter of the interface
  prompter        :: String,
  -- | error String, any error occurance has to fill
  -- this String with an error message
  errorMsg        :: String,
  -- | any function that needs to print something on the
  -- screen should use this generalOutput to store the output
  generalOutput   :: String,
  -- | open comment
  openComment     :: Bool,
  -- | history for undo command
  undoHistoryList :: [String],
  -- | history for redo command
  redoHistoryList :: [String],
  -- | for undo function history
  oldEnv          :: Maybe LibEnv 
 }



-- | Creates an initial state of the CMDL interface
emptyCMDLState :: CMDLState
emptyCMDLState =
    CMDLState {
        devGraphState = Nothing,
        proveState    = Nothing,
        prompter      = "> ",
        errorMsg      = "",
        generalOutput = "",
        openComment   = False,
        undoHistoryList = [],
        redoHistoryList = [],
        oldEnv        = Nothing
        }

-- | Returns the list of all nodes, if it is not up to date
-- the function recomputes the list
getAllNodes :: CMDLDevGraphState -> [LNode DGNodeLab]
getAllNodes state
 = case allNodesUpToDate state of
    -- nodes are up to date
    True -> allNodes state
    -- nodes are not up to date
    False -> labNodesDG $ lookupDGraph (ln state)
                             (libEnv state)


--local function that computes the theory of a node 
--that takes into consideration translated theories in 
--the selection too and returns the theory as a string
getTh :: Int -> CMDLState -> Maybe G_theory
getTh x state
 = let
    -- compute the theory for a given node 
    -- (see Static.DGToSpec) 
       fn n = case devGraphState state of
                Nothing -> Nothing
                Just dgState ->
                 case computeTheory (libEnv dgState)
                               (ln dgState) n of
                  Result _ (Just th) -> Just th
                  _                  -> Nothing
   in case proveState state of
       Nothing -> fn x
       Just ps ->
        case find (\y -> case y of
                          Element _ z -> z == x) $
                  elements ps of
         Nothing -> fn x
         Just _ -> 
           case cComorphism ps of
            Nothing -> fn x
            Just cm -> 
              case fn x of
               Nothing -> Nothing
               Just sth->
                case mapG_theory cm sth of
                  Result _ Nothing -> Just sth
                  Result _ (Just sth') -> Just sth'



-- | Given a list of node names and the list of all nodes
-- the function returns all the nodes that have their name
-- in the name list but are also goals
obtainGoalNodeList :: CMDLState -> [String] -> [LNode DGNodeLab]
                               -> ([String],[LNode DGNodeLab])
obtainGoalNodeList state input ls
 = let (l1,l2) = obtainNodeList input ls 
       l2' = filter (\(nb,nd) -> 
                       let nwth = getTh nb state 
                       in case nwth of
                           Nothing -> False
                           Just th -> nodeContainsGoals (nb,nd) th) l2
   in (l1,l2')




-- | Returns the list of all nodes that are goals, 
-- taking care of the up to date status
getAllGoalNodes :: CMDLState -> CMDLDevGraphState -> [LNode DGNodeLab]
getAllGoalNodes st state
 = filter (\(nb,nd) ->
             let nwth = getTh nb st
             in case nwth of
                 Nothing -> False
                 Just th -> nodeContainsGoals (nb,nd) th) $
                                                     getAllNodes state

-- | Returns the list of all edges, if it is not up to date
-- the funcrion recomputes the list
getAllEdges :: CMDLDevGraphState -> [LEdge DGLinkLab]
getAllEdges state
 = case allEdgesUpToDate state of
    -- edges are up to date
    True -> allEdges state
    -- edges are not up to date
    False -> labEdgesDG $ lookupDGraph (ln state)
                            (libEnv state)

-- | Returns the list of all goal edges taking care of the
-- up to date status
getAllGoalEdges :: CMDLDevGraphState -> [LEdge DGLinkLab]
getAllGoalEdges state
 = filter edgeContainsGoals $ getAllEdges state


-- | Datatype describing the types of commands according 
-- to what they expect as input
data CommandTypes = 
-- requires nodes 
   ReqNodes 
-- requires edges
 | ReqEdges
-- requires nodes and edges
 | ReqNodesAndEdges
-- requires provers
 | ReqProvers
-- requires comorphisms
 | ReqComorphism
-- requires a file (*.casl)
 | ReqFile
-- require goal nodes
 | ReqGNodes
-- require goal edges
 | ReqGEdges
-- require goal noes and edges
 | ReqGNodesAndGEdges
-- require axioms name
 | ReqAxm
-- require goals
 | ReqGoal
-- not recognized
 | ReqUnknown

-- | Datatype describing the list of possible action on a list
-- of selected items
data ActionType =
   ActionSet
 | ActionSetAll
 | ActionDel
 | ActionDelAll
 | ActionAdd

data GoalAxm =
   TypeGoal
 | TypeAxm
