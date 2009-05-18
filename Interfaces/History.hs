{- |
Module      :$Header$
Description : history management functions
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

Interfaces.History contains different functions that deal
with history

-}

module Interfaces.History
         ( undoOneStep
         , redoOneStep
         , undoOneStepWithUpdate
         , redoOneStepWithUpdate
         , add2history
         ) where

import Interfaces.DataTypes
import Interfaces.Command
import Common.LibName

import Proofs.AbstractState
import Proofs.EdgeUtils

import Static.DevGraph

import qualified Data.Map as Map
import Data.List

-- | Datatype used to differentiate between the two actions (so that code does
-- not get duplicated
data UndoOrRedo =
   DoUndo
 | DoRedo

add2history :: Command -> IntState -> [UndoRedoElem] -> IntState
add2history nm st descr = let
  hst = i_hist st
  ul = undoList hst
  nwEl = CmdHistory
    { command = nm
    , cmdHistory = descr }
  in st { i_hist = hst { undoList = nwEl : ul } }

-- | Undo or redo a command that modified the development graph
undoRedoDgCmd :: UndoOrRedo -> IntState -> LIB_NAME -> ([DGChange] -> IO ())
              -> IO IntState
undoRedoDgCmd actionType state ln update =
  case i_state state of
    -- should I return an error message??
   Nothing ->  return state
   Just dgS -> do
     let
         -- take ln from the history storage ??
         -- in contrast to GUI here you operate with only one ln at a time
         dg = lookupDGraph ln (i_libEnv dgS)
         (dg',changes) = ( case actionType of
                       DoUndo -> undoHistStep
                       DoRedo -> redoHistStep) dg
         newEnv = Map.insert ln dg' (i_libEnv dgS)
         newst = state {
                        i_state = Just $ dgS {
                                            i_libEnv = newEnv
                                            }
                       }
     update changes
     return newst

-- | Analyze changes to the selected nodes, return new nodes plus a list
-- of changes that would undo last changes
processList :: [ListChange]-> [Int_NodeInfo]
            -> [ListChange] -> ([Int_NodeInfo],[ListChange])
processList ls elems acc
 = case ls of
    -- if nothing to process return elements and changes
    [] -> (elems, acc)
    x:l->
      -- else check what type of change we are dealing with
      case x of
       -- if it is a change in axioms
       AxiomsChange nwaxms nb ->
         -- apply change and store the undo action
         let nwls = map (\y ->
                          case y of
                           Element ps nb' ->
                            case nb' == nb of
                             True ->((Element ps{includedAxioms = nwaxms} nb)
                                     ,[AxiomsChange (includedAxioms ps) nb])
                             False -> (y,[]) ) elems
             nwelems = map (\y -> fst y) nwls
             changesLs = concatMap (\y-> snd y) nwls
         in processList l nwelems (changesLs ++ acc)
       -- if it is a change in goals
       GoalsChange nwgls nb ->
         -- apply change and store the undo action
         let nwls = map (\y ->
                          case y of
                           Element ps nb' ->
                            case nb' == nb of
                             True ->((Element ps{selectedGoals = nwgls} nb)
                                     ,[GoalsChange (selectedGoals ps) nb])
                             False ->(y,[])) elems
             nwelems = map (\y -> fst y) nwls
             changeLs = concatMap (\y ->snd y) nwls
         in processList l nwelems (changeLs ++ acc)
       -- if selected nodes change
       NodesChange nwelems ->
         processList l nwelems ((NodesChange elems):acc)

-- | Process one step of undo or redo
processAny :: UndoOrRedo -> IntState -> (LIB_NAME -> [DGChange] -> IO ())
           -> IO IntState
processAny actype state update = do
  let hst = case actype of
              -- find out the list of actions according to the action
              -- (undo/redo)
              DoUndo -> undoList $ i_hist state
              DoRedo -> redoList $ i_hist state
  case hst of
    [] -> return state
    x:l-> do
       (nwst,ch) <- processUndoRedoElems actype (cmdHistory x) state [] update
       let
         x' = x { cmdHistory = ch }
         i_hist_state = i_hist state
         nwstate = case actype of
                    DoUndo -> nwst {
                              i_hist = IntHistory {
                                        undoList = l,
                                        redoList = x' : redoList i_hist_state
                                        }
                              }
                    DoRedo -> nwst {
                              i_hist = IntHistory {
                                        redoList = l,
                                        undoList = x' : undoList i_hist_state
                                        }
                              }
       return nwstate

-- | Process a list of undo or redo changes
processUndoRedoElems :: UndoOrRedo -> [UndoRedoElem] -> IntState
                     -> [UndoRedoElem] -> (LIB_NAME -> [DGChange] -> IO ())
                     -> IO (IntState,[UndoRedoElem])
processUndoRedoElems actype ls state acc update
 = case i_state state of
    Nothing -> return (state,[])
    Just ist ->
     case ls of
      [] -> return (state,acc)
      (UseThmChange sw):l -> do
         let nwst = state {
                      i_state = Just $ ist { useTheorems = sw } }
             ch   = UseThmChange $ useTheorems ist
         processUndoRedoElems actype l nwst (ch:acc) update
      (Save2FileChange sw):l -> do
         let nwst = state {
                      i_state = Just $ ist { save2file = sw }  }
             ch   = Save2FileChange $ save2file ist
         processUndoRedoElems actype l nwst (ch:acc) update
      (ProverChange nwp):l -> do
         let nwst = state {
                      i_state = Just $ ist { prover = nwp } }
             ch   = ProverChange $ prover ist
         processUndoRedoElems actype l nwst (ch:acc) update
      (ConsCheckerChange nwc):l -> do
         let nwst = state {
                      i_state = Just $ ist { consChecker = nwc} }
             ch   = ConsCheckerChange $ consChecker ist
         processUndoRedoElems actype l nwst (ch:acc) update
      (ScriptChange nws):l -> do
         let nwst = state {
                      i_state = Just $ ist { script = nws } }
             ch   = ScriptChange $ script ist
         processUndoRedoElems actype l nwst (ch:acc) update
      (LoadScriptChange sw):l -> do
         let nwst = state {
                      i_state = Just $ ist { loadScript = sw } }
             ch   = LoadScriptChange $ loadScript ist
         processUndoRedoElems actype l nwst (ch:acc) update
      (CComorphismChange nwc):l -> do
         let nwst = state {
                      i_state = Just $ ist { cComorphism = nwc} }
             ch   = CComorphismChange $ cComorphism ist
         processUndoRedoElems actype l nwst (ch:acc) update
      (DgCommandChange nln):l -> do
         nwst <- undoRedoDgCmd actype state nln $ update nln
         let ch = DgCommandChange nln
         processUndoRedoElems actype l nwst (ch:acc) update
      (ListChange nls):l -> do
         let (nwels,lc) = processList nls (elements ist) []
             nwst = state {
                     i_state = Just $ ist { elements = nwels } }
             ch   = ListChange lc
         processUndoRedoElems actype l nwst (ch:acc) update
      (IStateChange nist):l -> do
         let nwst = state { i_state = nist }
             ch   = IStateChange $ Just ist
         processUndoRedoElems actype l nwst (ch:acc) update

undoOneStep :: IntState -> IO IntState
undoOneStep ist = processAny DoUndo ist (\ _ _ -> return ())

redoOneStep :: IntState -> IO IntState
redoOneStep ist = processAny DoRedo ist (\ _ _ -> return ())

undoOneStepWithUpdate :: IntState -> (LIB_NAME -> [DGChange] -> IO ())
                      -> IO IntState
undoOneStepWithUpdate = processAny DoUndo

redoOneStepWithUpdate :: IntState -> (LIB_NAME -> [DGChange] -> IO ())
                      -> IO IntState
redoOneStepWithUpdate = processAny DoRedo
