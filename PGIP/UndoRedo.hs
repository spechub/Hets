{- |
Module      : $Header$
Description : description of undo and redo functions
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.UnDoRedo contains the implementation of the undo and redo commads
-}

module PGIP.UndoRedo
       ( cUndo
       , cRedo
       ) where
-- import Text.ParserCombinators.Parsec

import System.IO

import Data.List
import Static.DevGraph


import Proofs.AbstractState
import Proofs.EdgeUtils

import qualified Data.Map as Map

-- import System.Console.Shell.ShellMonad

-- import PGIP.Shell
import PGIP.DgCommands
-- import PGIP.InfoCommands
import PGIP.DataTypes
import PGIP.DataTypesUtils
-- import PGIP.ProveCommands

-- | Local datatype used to differentiate between the two action (so that
-- code does not get duplicated
data UndoOrRedo =
   DoUndo
 | DoRedo

-- This function done the preliminary actions to leave the interface
-- in a operational state after an undo command or redo command
beforeEnding :: UndoOrRedo -> CMDL_State -> CMDL_State
beforeEnding actionType state
 = let ls = case actionType of
             DoUndo -> undoList $ history state
             DoRedo -> redoList $ history state
   in
    case ls of
     [] -> genMessage [] "Nothing to undo" state
     _ ->
      let action = head $ ls
          rest   = tail $ ls
          oH     = history state
      in case actionType of
          DoUndo ->
           genMessage [] ("Action '"++(head$cmdNames action)++
             "' is now undone")
             state {
               history = oH {
                     undoList = rest,
                     redoList = (action: (redoList oH))
                      }
                 }
          DoRedo ->
           genMessage [] ("Action '"++(head$cmdNames action)++
             "' is now redone")
             state {
               history = oH {
                    redoList = rest,
                    undoList = (action :(undoList oH))
                    }
                 }


-- This function describes the behaviour of undo when the last action
-- did not change the enviroment
noAction :: UndoOrRedo -> CMDL_State ->IO  CMDL_State
noAction actionType state =
  do
   return $ beforeEnding actionType state

dgCmd :: UndoOrRedo -> CMDL_State -> IO CMDL_State
dgCmd actionType state =
 do
  case devGraphState state of
    -- should I return an error message??
   Nothing -> return $ genMessage [] "No library loaded yet" state
   Just dgS ->
    case oldEnv $ history state of
     Nothing ->
      return $ genErrorMsg "Internal Error ! Please reload the library" state
     Just initEnv ->
      do
       let
        oldLn  = ln dgS
        old_Env= libEnv dgS
        dg     = lookupDGraph oldLn old_Env
        initdg = lookupDGraph oldLn initEnv
        hist  = case actionType of
                  DoUndo -> proofHistory dg
                  DoRedo -> redoHistory  dg
       if hist == [emptyHistory] then return state
         else
          do
           let
             change = head hist
             phist'     = case actionType of
                           DoUndo -> tail $ proofHistory dg
                           DoRedo -> change : (proofHistory dg)
             rhist'     = case actionType of
                           DoUndo -> change:(redoHistory dg)
                           DoRedo -> tail $ redoHistory dg
             dg'        = (applyProofHistory (init phist') initdg)
                          {redoHistory = rhist' }
             newEnv     = Map.insert oldLn dg' old_Env
             newst      = state {
                           devGraphState = Just dgS {
                                                 libEnv = newEnv
                                                 }
                                }
           return $ beforeEnding actionType newst


processList :: [CMDL_ListChange]-> [CMDL_ProofAbstractState]
               -> ([CMDL_ProofAbstractState],[CMDL_ListChange])
               -> ([CMDL_ProofAbstractState],[CMDL_ListChange])
processList ls elems (acc1,acc2)
 = case elems of
    [] -> (acc1,acc2)
    (Element ps nb):ll ->
     case find (\x -> case x of
                       AxiomsChange _ nb' -> nb == nb'
                       GoalsChange _ nb' -> nb == nb') ls of
      Nothing -> processList ls ll ((Element ps nb):acc1,acc2)
      Just smth ->
       case smth of
        AxiomsChange l _ ->
         processList ls ll ((Element ps {
                                     includedAxioms = l
                                     } nb) :acc1, (AxiomsChange
                                                (includedAxioms ps)
                                                nb):acc2)
        GoalsChange l _ ->
         processList ls ll ((Element ps {
                                     selectedGoals = l
                                     } nb):acc1, (GoalsChange
                                               (selectedGoals ps)
                                               nb):acc2)

redoAll:: CMDL_State -> IO CMDL_State
redoAll state
 = case snd $ head $ undoInstances $ history state of
    [] -> return state
    _ -> do
          nwSt <- proveCmd DoRedo state
          redoAll nwSt

-- | Creates from history the old prove state
genPs:: CMDL_State ->IO CMDL_State
genPs state
   -- function to find out the last call of select (dg basic)
 = let getScmd ls = case ls of
                     [] -> []
                     c:l -> case cmdType c of
                             SelectCmd   -> [c]
                             SelectCmdAll-> [c]
                             _ -> getScmd l
       -- find the last call of select
       scmd = getScmd $ undoList $ history state
   in case scmd of
       -- if such call not found then just end
       [] -> return state
       c:_ ->
        do
         -- else re-run the select command to create an initial prove state
         nwSt <- case cmdType c of
                  SelectCmd    -> cDgSelect (cmdInput c) state
                  SelectCmdAll -> cDgSelectAll state
                  _            -> return state
         -- get all the "done" action and exectue them
         let oH = history nwSt
             inst = undoInstances oH
             (uhist,_) = head $ inst
             nwSt' = nwSt {
                       history = oH {undoInstances = ([],uhist):(tail inst)}
                         }
         redoAll nwSt'

undoSelect :: CMDL_State -> IO CMDL_State
undoSelect state =
 do
  let oH = history state
      ul = head $ undoInstances oH
  return $ beforeEnding DoUndo
              ( state {
                      proveState = Nothing,
                      history = oH {
                                 undoInstances = tail $ undoInstances oH,
                                 redoInstances = ul:(redoInstances oH)
                                 }
                      })

-- undo commands using prove internal history
proveCmd :: UndoOrRedo -> CMDL_State -> IO CMDL_State
proveCmd actionType st =
 do
  state <- case actionType of
            DoRedo -> return st
            DoUndo -> case proveState st of
                       Just _ -> return st
                       Nothing -> genPs st
  case proveState state of
   Nothing -> return $ genMessage [] "Nothing selected" state
   Just pS ->
    case head $ undoInstances $ history state of
     ([],_) -> return $ genMessage [] "History is empty" state
     (uel,rel) ->
      do
       let cg   = case actionType of
                   DoUndo -> head uel
                   DoRedo -> head rel
           oH   = history state
           inst = tail $ undoInstances oH
           genNwst nwst el1 el2 = case actionType of
                                   DoUndo ->
                                    nwst {
                                     proveState = Just el1,
                                     history = oH {
                                      undoInstances= (tail uel,el2:rel):inst
                                      } }
                                   DoRedo ->
                                    nwst {
                                     proveState = Just el1,
                                     history = oH {
                                      undoInstances= (el2:uel,tail rel):inst
                                      } }
       case cg of
        UseThmChange x ->
         do
          let nwState = genNwst state (pS{useTheorems = x})
                              (UseThmChange $ useTheorems pS)
          return $ beforeEnding actionType nwState
        Save2FileChange x ->
         do
          let nwState = genNwst state (pS{save2file = x})
                               (Save2FileChange $ save2file pS)
          return $ beforeEnding actionType nwState
        ProverChange x ->
         do
          let nwState = genNwst state (pS{prover = x})
                               (ProverChange $ prover pS)
          return $ beforeEnding actionType nwState
        ConsCheckerChange x ->
         do
          let nwState = genNwst state(pS{consChecker = x})
                               (ConsCheckerChange $ consChecker pS)
          return $ beforeEnding actionType nwState
        ScriptChange x ->
         do
          let nwState = genNwst state (pS{script = x})
                               (ScriptChange $ script pS)
          return $ beforeEnding actionType nwState
        LoadScriptChange x ->
         do
          let nwState = genNwst state (pS{loadScript = x})
                               (LoadScriptChange $ loadScript pS)
          return $ beforeEnding actionType nwState
        CComorphismChange x ->
         do
          let nwState = genNwst state (pS{cComorphism = x})
                               (CComorphismChange $ cComorphism pS)
          return $ beforeEnding actionType nwState
        ProveChange x cls ->
         case devGraphState state of
          Nothing ->
           return $ genErrorMsg "Internal Error ! Please reload the library"
                                 state
          Just dgS ->
           do
            let nwDgS = dgS {
                         libEnv = x
                         }
                ls = elements pS
                nwls = concatMap(\(Element _ xx) ->
                                           selectANode xx nwDgS) ls
                (cgdls,ncgls) = processList cls nwls ([],[])
                nwst1 = genNwst state (pS{elements = cgdls})
                               (ProveChange (libEnv dgS) ncgls)
                nwState = nwst1 {
                         devGraphState = Just dgS {
                                           libEnv = x
                                           }
                          }
            return $ beforeEnding actionType nwState
        ListChange ls ->
         do
          let
           (cgdls,ncgls) = processList ls  (elements pS) ([],[])
           nwState = genNwst state (pS{elements = cgdls}) (ListChange ncgls)
          return $ beforeEnding actionType nwState

redoSelect :: CMDL_State -> IO CMDL_State
redoSelect state =
   do
    let cmdd = head $ redoList $ history state
    nwSt <- case cmdType cmdd of
              SelectCmd    -> do
                               cDgSelect (cmdInput cmdd) state
              SelectCmdAll -> do
                               cDgSelectAll state
              _            -> do
                               return state
    let oH = history nwSt
        ul = undoInstances oH
        rl = redoInstances oH
    return $beforeEnding DoRedo
             (nwSt {
                 history = oH {
                            redoInstances = tail rl,
                            undoInstances = (head rl): ul
                            }
                    })

processAny :: UndoOrRedo -> CMDL_State -> IO CMDL_State
processAny actype state =
 let hist = case actype of
             DoUndo -> undoList $ history state
             DoRedo -> redoList $ history state
 in
  do
   case hist of
     []  -> return $ genMessage [] "History empty" state
     x:_ -> case cmdType x of
             DgCmd -> dgCmd actype state
             InfoCmd -> noAction actype state
             ProveCmd -> proveCmd actype state
             SelectCmd -> case actype of
                          DoUndo -> undoSelect state
                          DoRedo -> redoSelect state
             SelectCmdAll -> case actype of
                              DoUndo -> undoSelect state
                              DoRedo -> redoSelect state
             EvalCmd -> proveCmd actype state
             SystemCmd -> noAction actype state
             UndoRedoCmd -> return state


-- | Undoes the last command entered
cUndo :: CMDL_State -> IO CMDL_State
cUndo state =
  do
   processAny DoUndo state

cRedo :: CMDL_State -> IO CMDL_State
cRedo state =
   processAny DoRedo state
