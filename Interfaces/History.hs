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
         , add2history
         ) where

import Interfaces.DataTypes
import Common.LibName

import Proofs.AbstractState
import Proofs.EdgeUtils

import Static.DevGraph

import qualified Data.Map as Map
import Data.List


import Control.Concurrent.MVar

-- | Datatype used to differentiate between the two actions (so that code does
-- not get duplicated
data UndoOrRedo =
   DoUndo
 | DoRedo


-- write2Hist :: IORef IntState -> String -> [UndoRedoElem] -> IO()
-- write2Hist iost name descr
--  = do
--    ost <- readIORef iost
--    let nwst = add2history name ost descr
--    writeIORef iost nwst

add2history :: String -> IntState -> [UndoRedoElem] -> IntState
add2history nm st descr
 = case undoList $ i_hist st of
    [] ->  let nwEl = Int_CmdHistoryDescription {
                             cmdName = nm,
                             cmdDescription = descr }
               hst = i_hist st
           in st{i_hist=hst{ undoList = nwEl:(undoList hst) } }
    h:r ->
      case cmdName h of
       [] -> let nwEl = h { cmdName = nm,
                            cmdDescription = descr ++ (cmdDescription h) }
                 hst = i_hist st
             in st{i_hist=hst{ undoList = nwEl:r }}
       _ -> let nwEl = Int_CmdHistoryDescription {
                             cmdName = nm,
                             cmdDescription = descr }
                hst = i_hist st
             in st{i_hist=hst{ undoList = nwEl :h:r } }




-- | Undo or redo a command that modified the development graph
undoRedoDgCmd :: UndoOrRedo -> IntState -> LIB_NAME -> IO IntState
undoRedoDgCmd actionType state ln =
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
     case openlock dg' of 
      Nothing -> return newst
      Just lock -> do
        mvar <- tryTakeMVar lock
        case mvar of 
          Nothing -> return newst
          Just applyHist -> do
            applyHist changes
            putMVar lock applyHist
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
processAny :: UndoOrRedo -> IntState -> IO IntState
processAny actype state = do
  let hst = case actype of
              -- find out the list of actions according to the action
              -- (undo/redo)
              DoUndo -> undoList $ i_hist state
              DoRedo -> redoList $ i_hist state
  case hst of
    [] -> return state
    x:l-> do
       (nwst,ch) <- processUndoRedoElems actype (cmdDescription x) state []
       let
         x' = x { cmdDescription = ch }
         nwstate = case actype of
                    DoUndo -> nwst {
                              i_hist = IntHistory {
                                        undoList = l,
                                        redoList =x':(redoList$ i_hist state)
                                        }
                              }
                    DoRedo -> nwst {
                              i_hist = IntHistory {
                                        redoList = l,
                                        undoList = x':(undoList$i_hist state)
                                        }
                              }
       return nwstate


-- | Process a list of undo or redo changes
processUndoRedoElems :: UndoOrRedo -> [UndoRedoElem] -> IntState
                           -> [UndoRedoElem] ->IO (IntState,[UndoRedoElem])
processUndoRedoElems actype ls state acc
 = case i_state state of
    Nothing -> return (state,[])
    Just ist ->
     case ls of
      [] -> return (state,acc)
      (UseThmChange sw):l -> do
         let nwst = state {
                      i_state = Just $ ist { useTheorems = sw } }
             ch   = UseThmChange $ useTheorems ist
         processUndoRedoElems actype l nwst (ch:acc)
      (Save2FileChange sw):l -> do
         let nwst = state {
                      i_state = Just $ ist { save2file = sw }  }
             ch   = Save2FileChange $ save2file ist
         processUndoRedoElems actype l nwst (ch:acc)
      (ProverChange nwp):l -> do
         let nwst = state {
                      i_state = Just $ ist { prover = nwp } }
             ch   = ProverChange $ prover ist
         processUndoRedoElems actype l nwst (ch:acc)
      (ConsCheckerChange nwc):l -> do
         let nwst = state {
                      i_state = Just $ ist { consChecker = nwc} }
             ch   = ConsCheckerChange $ consChecker ist
         processUndoRedoElems actype l nwst (ch:acc)
      (ScriptChange nws):l -> do
         let nwst = state {
                      i_state = Just $ ist { script = nws } }
             ch   = ScriptChange $ script ist
         processUndoRedoElems actype l nwst (ch:acc)
      (LoadScriptChange sw):l -> do
         let nwst = state {
                      i_state = Just $ ist { loadScript = sw } }
             ch   = LoadScriptChange $ loadScript ist
         processUndoRedoElems actype l nwst (ch:acc)
      (CComorphismChange nwc):l -> do
         let nwst = state {
                      i_state = Just $ ist { cComorphism = nwc} }
             ch   = CComorphismChange $ cComorphism ist
         processUndoRedoElems actype l nwst (ch:acc)
      (DgCommandChange nln):l -> do
         nwst <- undoRedoDgCmd actype state nln
         let ch = DgCommandChange nln
         processUndoRedoElems actype l nwst (ch:acc)
      (ListChange nls):l -> do
         let (nwels,lc) = processList nls (elements ist) []
             nwst = state {
                     i_state = Just $ ist { elements = nwels } }
             ch   = ListChange lc
         processUndoRedoElems actype l nwst (ch:acc)
      (IStateChange nist):l -> do
         let nwst = state { i_state = nist }
             ch   = IStateChange $ Just ist
         processUndoRedoElems actype l nwst (ch:acc)


undoOneStep :: IntState -> IO IntState
undoOneStep = processAny DoUndo


redoOneStep :: IntState -> IO IntState
redoOneStep = processAny DoRedo
