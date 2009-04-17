{- |
Module      : $Header$
Description : CMDL interface commands
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

CMDL.ProveCommands contains all commands (except prove\/consistency check)
related to prove mode
-}

module CMDL.ProveCommands
       ( cTranslate
       , cDropTranslations
       , cGoalsAxmGeneral
       , cProve
       , cProveAll
       , cSetUseThms
       , cSetSave2File
       , cEndScript
       , cStartScript
       , cTimeLimit
       , cNotACommand
       ) where

import CMDL.DataTypes
import CMDL.DataTypesUtils
import CMDL.Utils
import CMDL.DgCommands
import CMDL.ProveConsistency

import Static.GTheory

import Common.Result
import qualified Common.OrderedMap as OMap

import Data.List

import Comorphisms.LogicGraph

import Proofs.AbstractState

import Logic.Comorphism

import Control.Concurrent
import Control.Concurrent.MVar

import System.Posix.Signals
import System.IO

import Interfaces.GenericATPState
import Interfaces.DataTypes

-- | Drops any seleceted comorphism
cDropTranslations :: CMDL_State -> IO CMDL_State
cDropTranslations state =
 case i_state $ intState state of
   Nothing -> return $ genErrorMsg "Nothing selected" state
   Just pS ->
    case cComorphism pS of
     Nothing -> return state
     Just _ -> return $
       add2hist [CComorphismChange $ cComorphism pS] $
        state {
          intState = (intState state ) {
           i_state = Just $ pS {
              cComorphism = getIdComorphism $ elements pS } }
         }


-- | select comorphisms
cTranslate::String -> CMDL_State -> IO CMDL_State
cTranslate input state =
 case i_state $ intState state of
  -- nothing selected !
  Nothing -> return $ genErrorMsg "Nothing selected" state
  Just pS ->
   -- parse the comorphism name
   case lookupComorphism_in_LG $ trim input of
    Result _ Nothing -> return $ genErrorMsg "Wrong comorphism name" state
    Result _ (Just cm) ->
      case cComorphism pS of
       -- when selecting some theory the Id comorphism is automatically
       -- generated
       Nothing -> return $ genErrorMsg "No theory selected" state
       Just ocm ->
        case compComorphism ocm cm of
            Result _ Nothing ->
             return $ genErrorMsg "Can not add comorphism" state
            Result _ (Just smth) ->
              return $ genMessage [] "Adding comorphism"
                     $ add2hist [CComorphismChange $ cComorphism pS] $
                      state {
                        intState = (intState state) {
                         i_state = Just pS {
                                    cComorphism = Just smth } }
                          }


parseElements :: CMDL_ListAction -> [String] -> CMDL_GoalAxiom
                 -> [Int_NodeInfo]
                 -> ([Int_NodeInfo],[ListChange])
                 -> ([Int_NodeInfo],[ListChange])
parseElements action gls gls_axm elems (acc1,acc2)
 = case elems of
    [] -> (acc1,acc2)
    (Element st nb):ll ->
      let allgls = case gls_axm of
                    ChangeGoals -> OMap.keys $ goalMap st
                    ChangeAxioms-> case theory st of
                                 G_theory _ _ _ aMap _ ->
                                  OMap.keys aMap
          selgls = case gls_axm of
                    ChangeGoals -> selectedGoals st
                    ChangeAxioms-> includedAxioms st
          fn' x y = x==y
          fn ks x = case find (fn' x) $ ks of
                     Just _ ->
                      case action of
                       ActionDel -> False
                       _         -> True
                     Nothing ->
                      case action of
                       ActionDel  -> True
                       _          -> False
          gls' = case action of
                   ActionDelAll -> []
                   ActionDel -> filter (fn  selgls) gls
                   ActionSetAll -> allgls
                   ActionSet -> filter (fn allgls) gls
                   ActionAdd ->
                        nub $ (selgls)++ filter (fn allgls) gls
          nwelm = case gls_axm of
                   ChangeGoals  -> Element (st {selectedGoals = gls'}) nb
                   ChangeAxioms -> Element (st {includedAxioms= gls'}) nb
          hchg = case gls_axm of
                   ChangeGoals  -> GoalsChange (selectedGoals  st) nb
                   ChangeAxioms -> AxiomsChange(includedAxioms st) nb
       in parseElements action gls gls_axm ll (nwelm:acc1,hchg:acc2)

-- | A general function that implements the actions of setting,
-- adding or deleting goals or axioms from the selection list
cGoalsAxmGeneral :: CMDL_ListAction -> CMDL_GoalAxiom ->
                    String ->CMDL_State
                 -> IO CMDL_State
cGoalsAxmGeneral action gls_axm input state
 = case i_state $ intState state of
    Nothing -> return $ genErrorMsg "Nothing selected" state
    Just pS ->
     case elements pS of
      [] -> return $ genErrorMsg "Nothing selected" state
      ls ->
       do
        let gls = words input
        let (ls',hst) = parseElements action gls
                           gls_axm
                           ls ([],[])
        return $ add2hist [ListChange hst] $
                    state {
                      intState = (intState state) {
                        i_state = Just pS {
                                         elements = ls'
                                         }
                             }
                     }

-- | Proves only selected goals from all nodes using selected
-- axioms
cProve:: CMDL_State-> IO CMDL_State
cProve state
 = case i_state $ intState state of
    Nothing -> return $ genErrorMsg "Nothing selected" state
    Just pS ->
       do
        case elements pS of
         [] -> return $ genErrorMsg "Nothing selected" state
         ls ->
           do
            --create initial mVars to comunicate
            mlbEnv <- newMVar $ i_libEnv pS
            mSt    <- newMVar Nothing
            mThr   <- newMVar Nothing
            mW     <- newEmptyMVar
            -- fork
            thrID <- forkIO(proveLoop mlbEnv mThr mSt mW pS ls)
            -- install the handler that waits for SIG_INT
            installHandler sigINT (Catch $
                     sigIntHandler mThr mlbEnv mSt thrID mW (i_ln pS)
                                  ) Nothing
            -- block and wait for answers
            answ <- takeMVar mW
            let nwpS = pS {
                             i_libEnv = answ
                             }
            let nwls=concatMap(\(Element _ x) ->
                                              selectANode x nwpS) ls
                hst=concatMap(\(Element stt x)  ->
                                 (AxiomsChange (includedAxioms stt) x):
                                 (GoalsChange (selectedGoals stt) x):
                                   []) ls
            return $ add2hist [(DgCommandChange $ i_ln nwpS),
                               (ListChange hst)] $
                         state {
                           intState = (intState state) {
                            i_state = Just $ pS {
                                              elements = nwls } }
                            }

-- | Proves all goals in the nodes selected using all axioms and
-- theorems
cProveAll::CMDL_State ->IO CMDL_State
cProveAll state
 = case i_state $ intState state of
    Nothing -> return$ genErrorMsg "Nothing selected" state
    Just pS ->
       do
        case elements pS of
         [] -> return $ genErrorMsg "Nothing selected" state
         ls ->
           do
            let ls' = map (\(Element st nb) ->
                              case theory st of
                               G_theory _ _ _ aMap _ ->
                                Element
                                  (st {
                                     selectedGoals = OMap.keys $
                                                       goalMap st,
                                     includedAxioms = OMap.keys aMap,
                                     includedTheorems = OMap.keys $
                                                         goalMap st
                                    }) nb ) ls
            let nwSt = add2hist [ListChange [NodesChange $ elements pS]] $
                      state {
                       intState = (intState state) {
                         i_state = Just $ pS {
                                           elements = ls' } } }
            cProve nwSt

-- | Sets the use theorems flag of the interface
cSetUseThms :: Bool -> CMDL_State -> IO CMDL_State
cSetUseThms val state
 = case i_state $ intState state of
    Nothing -> return $ genErrorMsg "Norhing selected" state
    Just pS ->
     do
      return $ add2hist [UseThmChange $ useTheorems pS] $
          state {
           intState = (intState state) {
             i_state=  Just pS {
                             useTheorems = val } } }

-- | Sets the save2File value to either true or false
cSetSave2File :: Bool -> CMDL_State -> IO CMDL_State
cSetSave2File val state
 = case i_state $ intState state of
    Nothing -> return $ genErrorMsg "Nothing selected" state
    Just ps ->
     do
      return $ add2hist [Save2FileChange $ save2file ps] $
          state {
            intState = (intState state) {
             i_state = Just ps { save2file = val } } }


-- | The function is called everytime when the input could
-- not be parsed as a command
cNotACommand :: String -> CMDL_State -> IO CMDL_State
cNotACommand input state
 = do
    case input of
     -- if input line is empty do nothing
     [] -> return state
     -- anything else see if it is in a blocl of command
     s ->
      case i_state $ intState state of
        Nothing -> return $ genErrorMsg ("Error on input line :"++s) state
        Just pS ->
          case loadScript pS of
            False -> return$ genErrorMsg ("Error on input line :"++s) state
            True ->
             do
              let olds = script pS
                  oldextOpts = ts_extraOpts olds
              let nwSt = state {
                          intState = (intState state) {
                           i_state = Just pS {
                             script = olds { ts_extraOpts = s:oldextOpts }
                             } } }
              return $ add2hist [ScriptChange $ script pS] nwSt


-- | Function to signal the interface that the script has ended
cEndScript :: CMDL_State -> IO CMDL_State
cEndScript state
 = case i_state $ intState state of
    Nothing -> return $ genErrorMsg "Nothing selected" state
    Just ps ->
     case loadScript ps of
      False -> return $ genErrorMsg "No previous call of begin-script" state
      True ->
       do
        let nwSt= state {
                    intState = (intState state) {
                     i_state = Just ps {
                       loadScript = False } } }
        return $ add2hist [LoadScriptChange $ loadScript ps] nwSt

-- | Function to signal the interface that a scrips starts so it should
-- not try to parse the input
cStartScript :: CMDL_State-> IO CMDL_State
cStartScript state
 = do
    case i_state $ intState state of
     Nothing -> return $ genErrorMsg "Nothing selected" state
     Just ps ->
      return $ add2hist [LoadScriptChange $ loadScript ps] $
              state {
                intState = (intState state) {
                  i_state = Just ps {
                                 loadScript = True } } }

-- sets a time limit
cTimeLimit :: String -> CMDL_State-> IO CMDL_State
cTimeLimit input state
 = case i_state $ intState state of
    Nothing -> return $ genErrorMsg "Nothing selected" state
    Just ps ->
     case checkIntString $ trim input of
       False -> return $ genErrorMsg "Please insert a number of seconds" state
       True ->
        do
         let inpVal = (read $ trim input)::Int
         let oldS = script ps
         return $ add2hist [ScriptChange $ script ps] $
               state {
                 intState = (intState state) {
                  i_state = Just ps {
                              script = oldS {   ts_timeLimit = inpVal } } } }

