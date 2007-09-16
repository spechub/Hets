{- |
Module      :$Header$
Description : description of undo/redo functions
Copyright   : uni-bremen and DFKI
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.UndoRedo contains the implementation of the undo and redo commads
-} 

module PGIP.UndoRedo
       ( shellUndo
       , shellRedo
       ) where

import PGIP.CMDLState

import System.IO

import Data.List
import Static.DevGraph


import Proofs.AbstractState
import Proofs.EdgeUtils

import qualified Data.Map as Map

import System.Console.Shell.ShellMonad

import PGIP.CMDLShell
import PGIP.DgCommands
import PGIP.InfoCommands
-- This function done the preliminary actions to leave the interface
-- in a operational state after an undo command
undoEnd :: String->CMDLState -> CMDLState
undoEnd name state
 = case undoHistoryList state of
    [] -> state
    _ -> 
     let action = head $ undoHistoryList state
         rest   = tail $ undoHistoryList state
         redols = redoHistoryList state
     in state {
          undoHistoryList = rest,
          redoHistoryList = (action : redols),
          generalOutput = ("Action '"++name++"' is now undone.")
          }

-- This function describes the behaviour of undo when the last action
-- did not change the enviroment
undoNoAction :: String-> CMDLState ->IO  CMDLState
undoNoAction name state = 
  do
   return $ undoEnd name state

undoInternalHistory :: String -> CMDLState -> IO CMDLState
undoInternalHistory name state =
 do
  case devGraphState state of
    -- should I return an error message??
   Nothing -> return state 
   Just dgS ->
    case oldEnv state of 
     Nothing -> 
      return state {
              errorMsg="Internal Error ! Please reload the library"}
     Just initEnv ->
      do
       let 
        oldLn  = ln dgS
        old_Env= libEnv dgS
        dg     = lookupDGraph oldLn old_Env
        initdg = lookupDGraph oldLn initEnv
        phist  = proofHistory dg
        rhist  = redoHistory  dg
       if phist == [emptyHistory] then return state
         else 
          do
           let
             lastchange = head phist
             phist'     = tail phist
             rhist'     = lastchange:rhist
             dg'        = (applyProofHistory (init phist') initdg)
                          {redoHistory = rhist' }
             newEnv     = Map.insert oldLn dg' old_Env
             newst      = state {
                           devGraphState = Just dgS {
                                                 libEnv = newEnv
                                                 }
                                }
           return $ undoEnd name newst  


processList :: [ProofStatusChange]-> [CMDLProofAbstractState]
               -> ([CMDLProofAbstractState],[ProofStatusChange])
               -> ([CMDLProofAbstractState],[ProofStatusChange])
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

undoSelect :: String -> CMDLState -> IO CMDLState
undoSelect name state =
 do
  return $ undoEnd name ( state {
              proveState = Nothing
              })

-- undo commands using prove internal history
undoProveHistory :: String -> CMDLState -> IO CMDLState
undoProveHistory name state = 
 do
  case proveState state of 
   Nothing -> return state
   Just pS ->
    case historyList pS of
     ([],_) -> return state
     (uel,rel) ->
      do
       let cg = head uel
       case cg of
        UseThmChange x ->
         do
          let nwState = state {
                          proveState = Just pS {
                                        historyList = ( tail uel,
                                            (UseThmChange $ 
                                             useTheorems pS):rel),
                                        useTheorems = x
                                        }
                            }
          return $ undoEnd name nwState
        Save2FileChange x ->
         do 
          let nwState = state {
                          proveState = Just pS {
                                        historyList = (tail uel,
                                            (Save2FileChange $
                                             save2file pS):rel),
                                        save2file = x
                                        }
                           }
          return $ undoEnd name nwState                 
        ProverChange x ->
         do
          let nwState = state {
                          proveState = Just pS {
                                        historyList = (tail uel,
                                            (ProverChange $
                                             prover pS):rel),
                                        prover = x
                                        }
                               }
          return $ undoEnd name nwState
        ScriptChange x ->
         do
          let nwState = state {
                          proveState = Just pS {
                                        historyList = (tail uel,
                                             (ScriptChange $
                                              script pS):rel),
                                        script = x
                                        }
                              }
          return $ undoEnd name nwState
        LoadScriptChange x ->  
         do
          let nwState = state {
                         proveState = Just pS {
                                       historyList = (tail uel,
                                            (LoadScriptChange $
                                             loadScript pS):rel),
                                       loadScript = x
                                       }
                         }
          return $ undoEnd name nwState
        CComorphismChange x ->
         do
          let nwState = state {
                         proveState = Just pS {
                                       historyList = (tail uel,
                                            (CComorphismChange $
                                             cComorphism pS):rel),
                                       cComorphism = x
                                       }
                          }
          return $ undoEnd name nwState
        ProveChange x cls ->
         case devGraphState state of
          Nothing ->
           return state {
              errorMsg="Internal Error ! Please reload the library" }
          Just dgS ->    
           do
            let nwDgS = dgS {
                         libEnv = x
                         }
                ls = elements pS         
                nwls = concatMap(\(Element _ xx) ->
                                           selectANode xx nwDgS) ls
                (cgdls,ncgls) = processList cls nwls ([],[])
                nwState = state {
                         proveState = Just pS {
                                       historyList = (tail uel,
                                          (ProveChange 
                                          (libEnv dgS) ncgls):rel),
                                       elements = cgdls },
                         devGraphState = Just dgS {
                                           libEnv = x
                                           }
                          } 
            return $ undoEnd name nwState               
        ListChange ls -> 
         do
          let
           (cgdls,ncgls) = processList ls  (elements pS) ([],[])
           nwState = state {
                      proveState = Just pS {
                                    historyList = (tail uel,
                                         (ListChange ncgls):rel),
                                    elements = cgdls
                                    }
                          }
          return $ undoEnd name nwState
           
-- | Undoes the last command entered
undo :: CMDLState -> IO CMDLState
undo state =
 case undoHistoryList state of
  [] -> return state
  _  ->
   do
    let action = head $ undoHistoryList state
    -- get the command name and input
        (cmd,input) = let wds = words action
                      in
                       case head wds of
                        "dg" -> ("dg "++ (head $ tail wds),
                                unwords $tail $tail wds)
                        "dg-all" -> ("dg-all "++(head$tail wds),
                                    unwords$tail$tail wds)
                        "add" -> ("add "++(head$tail wds),
                                 unwords$tail$tail wds)
                        "set"-> 
                          case head$tail wds of
                          "include-theorems"->(unwords wds,[])
                          "save-prove-to-file"->(unwords wds,[])
                          _ ->("set "++(head$tail wds),
                              unwords $ tail$tail wds)
                        "del" ->("del "++(head$tail wds),
                                unwords$tail$tail wds)
                        "set-all"->("set-all "++(head$tail wds),
                                   unwords$tail$tail wds)
                        "del-all"->("del-all "++(head$tail wds),
                                   unwords$tail$tail wds)
                        _ -> (head wds, unwords$tail wds)
    case cmd of
     --
     "dg loc-decomp" -> undoInternalHistory ("dg loc-decomp "++input)
                                         state
     --
     "nodes" -> undoNoAction "nodes" state
     --
     "show-dg-goals" -> undoNoAction "show-dg-goals" state
     --
     "dg loc-infer" -> undoInternalHistory ("dg loc-infer "++input)
                              state
     --
     "prove" -> undoProveHistory ("prove "++input) state
     --
     "show-graph" -> undoNoAction "show-graph" state 
     --
     "dg thm-hide" -> undoInternalHistory ("dg thm-hide "++input) 
                                 state
     --
     "prove-all" -> undoProveHistory ("prove-all "++input) state
     --
     "show-proven-goals" -> undoNoAction ("show-proven-goals "++input)
                                       state
     --
     "dg-all auto" -> undoInternalHistory "dg-all auto" state
     --
     "prover" -> undoProveHistory ("prover "++input) state
     --
     "show-proven-goals-current" ->
                undoNoAction "show-proven-goals-current" state
     --
     "dg-all basic" -> undoSelect "dg-all basic" state
     --
     "show-redo-history" -> undoNoAction "show-redo-history" state
     --
     "add axioms" -> undoProveHistory ("add axioms "++input) state
     --
     "dg-all comp" -> undoInternalHistory "dg-all comp" state
     --
     "select" -> undoSelect ("select "++input) state
     --
     "show-taxonomy" -> undoNoAction ("show-taxonomy "++input) state
     --
     "add goals" -> undoInternalHistory ("add goals "++input) state
     --
     "dg-all comp-new" -> undoInternalHistory "dg-all comp-new" state
     --
     "select-all" -> undoSelect "select-all" state
     --
     "show-taxonomy-current" -> 
                undoNoAction "show-taxonomy-current" state
     --
     "dg-all glob-decomp" -> undoInternalHistory "dg-all glob-decomp"
                                     state
     --
     "set axioms" -> undoProveHistory ("set axioms "++input) state
     --
     "show-theory" -> undoNoAction ("show-theory "++input) state
     --
     "del axioms" -> undoProveHistory ("del axioms "++input) state
     --
     "dg-all glob-subsume" -> undoInternalHistory "dg-all glob-subsume"
                                    state
     --
     "set goals" -> undoProveHistory ("set goals "++input) state
     --
     "show-theory-current" -> undoNoAction "show-theory-current" state
     --
     "del goals" -> undoProveHistory ("del goals "++input) state
     --
     "dg-all hide-thm" -> undoInternalHistory "dg-all hide-thm" state
     --
     "set include-theorems false" -> 
             undoProveHistory "set include-theorems false" state
     --
     "show-theory-goals" -> undoNoAction ("show-theory-goals "++input)
                                      state
     --
     "del-all axioms" -> undoProveHistory ("del-all axioms "++input) 
                               state
     --
     "dg-all loc-decomp" -> undoInternalHistory "dg-all loc-decomp" 
                                         state
     --
     "set include-theorems true" -> undoProveHistory 
                                     "set include-theorems true" state
     --
     "show-theory-goals-current" ->
            undoNoAction "show-theory-goals-current" state
     --
     "del-all goals" -> undoProveHistory ("del-all goals "++input)
                            state
     --
     "dg-all loc-infer" -> undoInternalHistory 
                                   "dg-all loc-infer" state
     --
     "set save-prove-to-file false" -> 
         undoProveHistory "set save-prove-to-file false" state
     --
     "show-undo-history" -> undoNoAction "show-undo-history" state
     --
     "details" -> undoNoAction "details" state
     --
     "dg-all thm-hide" -> undoInternalHistory "dg-all thm-hide" state
     --
     "set save-prove-to-file true" ->
        undoProveHistory "set save-prove-to-file true" state
     --
     "show-unproven-goals" -> undoNoAction 
                                 ("show-unproven-goals "++input) state
     --
     "dg auto" -> undoInternalHistory ("dg auto "++input) state
     --
     "edges" -> undoNoAction "edges" state
     --
     "set time-limit" -> undoProveHistory ("set time-limit "++input) 
                                state
     --
     "show-unproven-goals-current" ->
              undoNoAction "show-unproven-goals-current" state
     --
     "dg basic" -> undoSelect ("dg basic "++input) state
     --
     "end-script" -> undoProveHistory ("end-script "++input) state
     --
     "begin-script" -> undoProveHistory ("begin-script "++input) state
     --
     "set-all axioms" -> undoProveHistory ("set-all axioms "++input) 
                                     state
     --
     "translate" -> undoProveHistory ("translate "++input)
                                state
     --
     "dg comp" -> undoInternalHistory ("dg comp "++input) state 
     --
     "set-all goals" -> undoProveHistory ("set-all goals "++input)
                                state
     --
     "use" -> undoNoAction ("use "++input) state
     --
     "dg comp-new" -> undoInternalHistory ("dg comp-new "++input)
                                       state
     --
     "show-axioms" -> undoNoAction ("show-axioms "++input) state
     --
     "dg glob-decomp" -> undoInternalHistory 
                             ("dg glob-decomp "++input) state
     --
     "info" -> undoNoAction ("info "++input) state
     --
     "show-axioms-current"-> undoNoAction "show-axioms-current" state
     --
     "dg glob-subsume" -> undoInternalHistory 
                            ("dg glob-subsume "++input) state
     --
     "info-current" -> undoNoAction "info-current" state
     --
     "show-concept"-> undoNoAction ("show-concept "++input) state
     --
     "dg hide-thm" -> undoInternalHistory ("dg hide-thm "++input)
                                    state
     --
     "node-number" -> undoNoAction ("node-number "++input) state
     --
     "show-concept-current" ->
             undoNoAction "show-concept-current" state
     --
     _             -> return state {
                         errorMsg = "Internal error!"
                         }

shellUndo :: Sh CMDLState ()
shellUndo
 = shellComWithout undo False False "undo"

shellRedo :: Sh CMDLState ()
shellRedo
 = shellComWithout redo False False "redo"


redoEnd :: String -> CMDLState -> CMDLState
redoEnd name state
 = case redoHistoryList state of
    [] -> state
    _  ->
     let action = head $ redoHistoryList state
         rest   = tail $ redoHistoryList state
         undols = undoHistoryList state
     in state {
          redoHistoryList = rest,
          undoHistoryList = (action : undols),
          generalOutput = ("Action '"++name++"' is now redone.")
          }

redoNoAction :: String -> CMDLState -> IO CMDLState
redoNoAction name state =
 do
  return $ redoEnd name state

redoInternalHistory :: String -> CMDLState -> IO CMDLState
redoInternalHistory name state =
 do
  case devGraphState state of
   Nothing -> return state
   Just dgS ->
    case oldEnv state of
     Nothing ->
      return state {
              errorMsg = "Internal Error ! Please reload the library"}
     Just initEnv ->
      do
       let
        oldLn   = ln dgS
        old_Env = libEnv dgS
        dg      = lookupDGraph oldLn old_Env
        initdg  = lookupDGraph oldLn initEnv
        phist   = proofHistory dg
        rhist   = redoHistory dg
       if rhist == [emptyHistory] then return state
         else
          do
           let
             nextchange = head rhist
             rhist' = tail rhist
             phist' = nextchange:phist
             dg' = (applyProofHistory (init phist') initdg)
                   { redoHistory = rhist'}
             newEnv = Map.insert oldLn dg' old_Env
             newst = state {
                      devGraphState = Just dgS {
                                            libEnv = newEnv
                                            }
                            }
           return $ redoEnd name newst

redoSelect :: String -> String -> String ->CMDLState -> IO CMDLState
redoSelect name cmd input state =
 case cmd of
  "select" ->
    do
     nwState <- cDgSelect input state
     return $ redoEnd name nwState
  "dg basic" ->
    do
     nwState <- cDgSelect input state
     return $ redoEnd name nwState
  "select-all" ->
    do
     nwState <- cDgSelectAll state
     return $ redoEnd name nwState
  "dg-all basic" ->
    do
     nwState <- cDgSelectAll state
     return $ redoEnd name nwState
  _ -> return state {
          errorMsg = "Internal error! Please reload the library " }

redoProveHistory :: String -> CMDLState -> IO CMDLState
redoProveHistory name state =
 do
  case proveState state of
   Nothing -> return state
   Just pS ->
    case historyList pS of
     (_,[])-> return state
     (uel,rel) ->
      do
       let cg = head rel
       case cg of
        UseThmChange x ->
         do
          let nwState = state {
                          proveState = Just pS {
                                        historyList=((UseThmChange $
                                            useTheorems pS):uel, 
                                            tail rel),
                                        useTheorems = x
                                        }
                             }
          return $ redoEnd name nwState
        Save2FileChange x ->
         do
          let nwState = state {
                         proveState = Just pS {
                                       historyList = (
                                         (Save2FileChange $
                                          save2file pS):uel,
                                          tail rel),
                                       save2file = x
                                       }
                           }
          return $ redoEnd name nwState
        ProverChange x ->
         do
          let nwState = state {
                         proveState = Just pS {
                                       historyList = (
                                         (ProverChange $
                                         prover pS):uel,
                                         tail rel),
                                       prover = x
                                       }
                           }
          return $ redoEnd name nwState
        ScriptChange x ->
         do
          let nwState = state {
                         proveState = Just pS {
                                       historyList = (
                                         (ScriptChange $
                                         script pS):uel,
                                         tail rel),
                                       script = x
                                       }
                        }
          return $ redoEnd name nwState
        LoadScriptChange x ->
         do
          let nwState = state {
                         proveState = Just pS{
                                       historyList = (
                                         (LoadScriptChange $
                                         loadScript pS):uel,
                                         tail rel),
                                       loadScript = x
                                       }
                           }
          return $ redoEnd name nwState
        CComorphismChange x ->
         do 
          let nwState = state {
                         proveState = Just pS {
                                       historyList = (
                                         (CComorphismChange $
                                          cComorphism pS):uel,
                                          tail rel),
                                       cComorphism = x
                                       }
                            }
          return $ redoEnd name nwState
        ProveChange x cls ->
         case devGraphState state of
          Nothing ->
           return state {
             errorMsg = "Internal Error ! Please reload the library" }
          Just dgS ->
           do
            let nwDgS = dgS {
                          libEnv = x
                          }
                ls = elements pS
                nwls = concatMap(\(Element _ xx) ->
                                           selectANode xx nwDgS) ls
                (cgdls,ncgls) = processList cls nwls ([],[])
                nwState = state {
                         proveState = Just pS {
                                      historyList = (
                                         (ProveChange (libEnv dgS) 
                                         ncgls):uel, tail rel),
                                      elements = cgdls },
                         devGraphState = Just dgS {
                                           libEnv = x
                                           }
                         }
            return $ redoEnd name nwState
        ListChange ls ->
         do
          let 
           (cgdls,ncgls) = processList ls (elements pS) ([],[])
           nwState = state {
                      proveState = Just pS {
                                    historyList = (
                                      (ListChange ncgls):uel,
                                       tail rel),
                                    elements = cgdls
                                    }
                         }
          return $ redoEnd name nwState




-- | Redo th last command entered
redo :: CMDLState -> IO CMDLState
redo state =
 case redoHistoryList state of
  [] -> return state
  _ -> 
   do 
    let action = head $ redoHistoryList state
        (cmd,input) = let wds = words action
                      in
                       case head wds of
                        "dg" -> ("dg "++(head $ tail wds),
                                unwords $ tail $ tail wds)
                        "dg-all" -> ("dg-all "++(head$tail wds),
                                    unwords $ tail $tail wds)
                        "add" -> ("add "++(head$tail wds),
                                 unwords$tail $tail wds)
                        "set" ->
                          case head$tail wds of
                          "include-theorems" -> (unwords wds, [])
                          "save-prove-to-file"->(unwords wds, [])
                          _ -> ("set "++(head$tail wds),
                               unwords $ tail $ tail wds)
                        "del"-> ("del "++(head$tail wds),
                                unwords$tail$tail wds)
                        "set-all"->("set-all "++(head$tail wds),
                                   unwords$tail$tail wds)
                        "del-all"->("del-all "++(head$tail wds),
                                   unwords$tail$tail wds)
                        _ -> (head wds, unwords$tail wds)
    case cmd of
     --
     "dg loc-decomp" -> redoInternalHistory ("dg loc-decomp "++input)
                                       state
     --
     "nodes" -> 
      do
       nwst <- cNodes state 
       redoNoAction "nodes" nwst
     --
     "show-dg-goals" -> 
      do
       nwst <- cShowDgGoals state 
       redoNoAction "show-dg-goals" nwst
     --
     "dg loc-infer" -> redoInternalHistory ("dg loc-infer "++input)
                                 state
     --
     "prove" -> redoProveHistory ("prove "++input) state
     --
     "show-graph" -> 
      do
       nwst <- cDisplayGraph state 
       redoNoAction "show-graph" nwst
     --
     "dg thm-hide" -> redoInternalHistory ("dg thm-hide "++input)
                                 state
     --
     "prove-all" -> redoProveHistory ("prove-all "++input) state
     --
     "show-proven-goals" -> 
       do
        nwst <- cShowNodePGoals input state 
        redoNoAction ("show-proven-goals") nwst
     --
     "dg-all auto" -> redoInternalHistory "dg-all auto" state
     --
     "prover" -> redoProveHistory ("prover "++input) state
     --
     "show-proven-goals-current" ->
       do
         nwst <- cShowNodePGoalsCurrent state
         redoNoAction "show-proven-goals-current" nwst
     --
     "dg-all basic" -> redoSelect "dg-all basic" cmd input state
     --
     "show-redo-history" -> 
      do
       nwst <- cRedoHistory state 
       redoNoAction "show-redo-history" nwst
     --
     "add axioms" -> redoProveHistory ("add axioms "++input) state
     --
     "dg-all comp" -> redoInternalHistory "dg-all comp" state
     --
     "select" -> redoSelect ("select "++input) cmd input state
     --
     "show-taxonomy" -> 
       do
        nwst <- cShowTaxonomy input state 
        redoNoAction ("show-taxonomy "++input) nwst
     --
     "add goals"-> redoInternalHistory ("add goals "++input) state
     --
     "dg-all comp-new" -> redoInternalHistory "dg-all comp-new" state
     --
     "select-all" -> redoSelect "select-all" cmd input state
     --
     "show-taxonomy-current" ->
       do
        nwst <- cShowTaxonomyCurrent state
        redoNoAction "show-taxonomy-current" nwst
     --
     "dg-all glob-decomp" -> redoInternalHistory "dg-all glob-decomp"
                                     state
     --
     "set axioms" -> redoProveHistory ("set axioms "++input) state
     --
     "show-theory" -> 
      do
       nwst <- cShowTheory input state 
       redoNoAction ("show-theory "++input) nwst
     --
     "del axioms" -> redoProveHistory ("del axioms "++input) state
     --
     "dg-all glob-subsume" -> redoInternalHistory "dg-all glob-subsume"
                                    state
     --
     "set goals" -> redoProveHistory ("set goals "++input) state
     --
     "show-theory-current" -> 
      do
        nwst <- cShowTheoryCurrent state
        redoNoAction "show-theory-current" nwst
     --
     "del goals" -> redoProveHistory ("del goals "++input) state
     --
     "dg-all hide-thm" -> redoInternalHistory "dg-all hide-thm" state
     --
     "set include-theorems false" ->
             redoProveHistory "set include-theorems false" state
     --
     "show-theory-gols" -> 
      do
       nwst <- cShowTheoryGoals input state
       redoNoAction ("show-theory-goals "++input) nwst
     --
     "del-all axioms" -> redoProveHistory ("del-all axioms "++input)
                               state
     --
     "dg-all loc-decomp" -> redoInternalHistory "dg-all loc-decomp"
                                         state
     --
     "set include-theorems true" -> redoProveHistory
                                     "set include-theorems true" state
     --
     "show-theory-goals-current" -> 
      do
       nwst <- cShowTheoryGoalsCurrent state
       redoNoAction "show-theory-goals-current" nwst
     --
     "del-all goals" -> redoProveHistory ("del-all goals "++input)
                            state
     --
     "dg-all loc-infer" -> redoInternalHistory 
                                   "dg-all loc-infer" state
     --
     "set save-prove-to-file false" -> 
         redoProveHistory "set save-prove-to-file false" state
     --
     "show-undo-history" -> 
      do
       nwst <- cUndoHistory state 
       redoNoAction "show-undo-history" nwst
     --
     "details" -> 
      do
       nwst <- cDetails state
       redoNoAction "details" nwst
     --
     "dg-all thm-hide" -> redoInternalHistory "dg-all thm-hide" state
     --
     "set save-prove-to-file true" ->
        redoProveHistory "set save-prove-to-file true" state
     --
     "show-unproven-goals" -> 
      do
       nwst <- cShowNodeUGoals input state
       redoNoAction ("show-unproven-goals "++input) nwst
     --
     "dg auto" -> redoInternalHistory ("dg auto "++input) state
     --
     "edges" -> 
      do
       nwst <- cEdges state
       redoNoAction "edges" nwst
     --
     "set time-limit" -> redoProveHistory ("set time-limit "++input)
                                state
     --
     "show-unproven-goals-current" ->
       do
        nwst <- cShowNodeUGoalsCurrent state
        redoNoAction "show-unproven-goals-current" nwst
     --
     "dg basic" -> redoSelect ("dg basic "++input) cmd input state
     --
     "end-script" -> redoProveHistory ("end-script "++input) state
     --
     "begin-script" -> redoProveHistory ("begin-script "++input) state
     --
     "set-all axioms" -> redoProveHistory ("set-all axioms "++input)
                                     state
     --
     "translate" -> redoProveHistory ("translate "++input) 
                                state
     --
     "dg comp" -> redoInternalHistory ("dg comp "++input) state
     --
     "set-all goals" -> redoProveHistory ("set-all goals "++input)
                               state
     --
     "use" -> redoNoAction ("use "++input) state
     --
     "dg comp-new" -> redoInternalHistory ("dg comp-new "++input)
                                       state
     --
     "show-axioms" -> 
       do
        nwst <- cShowNodeAxioms input state 
        redoNoAction ("show-axioms "++input) nwst 
     --
     "dg glob-decomp" -> redoInternalHistory
                             ("dg glob-decomp "++input) state
     --
     "info" -> 
      do
       nwst <- cInfo input state
       redoNoAction ("info "++input) nwst
     --
     "show-axioms-current" ->  
      do
       nwst <- cShowNodeAxiomsCurrent state
       redoNoAction "show-axioms-current" nwst
     --
     "dg glob-subsume" -> redoInternalHistory
                            ("dg glob-subsume "++input) state
     --
     "info-current" -> 
      do
       nwst <- cInfoCurrent state
       redoNoAction "info-current" nwst
     --
     "show-concept" -> 
       do
        nwst <- cShowConcept input state
        redoNoAction ("show-concept "++input) nwst
     --
     "dg hide-thm" -> redoInternalHistory ("dg hide-thm "++input)
                                    state
     --
     "node-number" -> 
       do
        nwst <- cNodeNumber input state
        redoNoAction ("node-number "++input) nwst
     --
     "show-concept-current" ->
        do
         nwst <- cShowConceptCurrent state
         redoNoAction "show-concept-current" nwst
     --
     _     -> return state {
                        errorMsg = "Internal error!"
                        }
     --
