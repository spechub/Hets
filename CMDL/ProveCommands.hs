{-# LANGUAGE CPP #-}
{- |
Module      : ./CMDL/ProveCommands.hs
Description : CMDL interface commands
Copyright   : uni-bremen and DFKI
License     : GPLv2 or higher, see LICENSE.txt
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
       , cDoLoop
       , cProve
       , cDisprove
       , cProveAll
       , cSetUseThms
       , cSetSave2File
       , cEndScript
       , cStartScript
       , cTimeLimit
       , cNotACommand
       , cShowOutput
       ) where

import CMDL.DataTypes (CmdlState (intState), CmdlGoalAxiom (..),
                      CmdlListAction (..), ProveCmdType (..))
import CMDL.DataTypesUtils (add2hist, genMsgAndCode, genMessage,
                            genAddMessage, getIdComorphism)

import CMDL.DgCommands (selectANode)
import CMDL.ProveConsistency (doLoop, sigIntHandler)
import CMDL.Utils (checkIntString)

import Common.Result (Result (Result))
import Common.Utils (trim, splitOn)

import Data.List (find, nub)
import Data.Maybe (fromMaybe)

import Comorphisms.LogicGraph (lookupComorphism_in_LG)

import Proofs.AbstractState

import Logic.Comorphism (compComorphism, AnyComorphism (..))
import Logic.Logic (language_name)

import Control.Concurrent (forkIO)
import Control.Concurrent.MVar (newEmptyMVar, newMVar, takeMVar)
import Control.Monad (foldM)

#ifdef UNIX
import System.Posix.Signals (Handler (Catch), installHandler, sigINT)
#endif

import Interfaces.GenericATPState (ATPTacticScript (tsTimeLimit, tsExtraOpts))
import Interfaces.DataTypes (ListChange (..), IntIState (..), Int_NodeInfo (..),
                            UndoRedoElem (..), IntState (i_state))

-- | Drops any seleceted comorphism
cDropTranslations :: CmdlState -> IO CmdlState
cDropTranslations state =
 case i_state $ intState state of
   Nothing -> return $ genMsgAndCode "Nothing selected" 1 state
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
cTranslate :: String -> CmdlState -> IO CmdlState
cTranslate input state' =
 foldM (\ state c -> case i_state $ intState state of
   -- nothing selected !
   Nothing -> return $ genMsgAndCode "Nothing selected" 1 state
   Just pS -> case lookupComorphism_in_LG c of
    Result m Nothing -> return $ genMsgAndCode (show m) 1 state
    Result _ (Just cm) ->
      case cComorphism pS of
       {- when selecting some theory the Id comorphism is automatically
          generated -}
       Nothing -> return $ genMsgAndCode "No theory selected" 1 state
       Just ocm ->
        case compComorphism ocm cm of
            Result _ Nothing ->
             return $ genMsgAndCode "Can not add comorphism" 1 state
            Result _ (Just smth) ->
              return $ genAddMessage [] ("Adding comorphism " ++
                        (\ (Comorphism c') -> language_name c') cm)
                     $ add2hist [CComorphismChange $ cComorphism pS] $
                      state {
                        intState = (intState state) {
                         i_state = Just pS {
                                    cComorphism = Just smth } }
                          }) (genMessage "" "" state')
                             (concatMap (splitOn ';') $
                              concatMap (splitOn ':') $
                              words $ trim input)


parseElements :: CmdlListAction -> [String] -> CmdlGoalAxiom
                 -> [Int_NodeInfo]
                 -> ([Int_NodeInfo], [ListChange])
                 -> ([Int_NodeInfo], [ListChange])
parseElements action gls gls_axm elems (acc1, acc2)
 = case elems of
    [] -> (acc1, acc2)
    Element st nb : ll ->
      let allgls = case gls_axm of
                    ChangeGoals -> map fst $ getGoals st
                    ChangeAxioms -> map fst $ getAxioms st
          selgls = case gls_axm of
                    ChangeGoals -> selectedGoals st
                    ChangeAxioms -> includedAxioms st
          fn' x y = x == y
          fn ks x = case find (fn' x) ks of
                     Just _ ->
                      case action of
                       ActionDel -> False
                       _ -> True
                     Nothing ->
                      case action of
                       ActionDel -> True
                       _ -> False
          gls' = case action of
                   ActionDelAll -> []
                   ActionDel -> filter (fn selgls) gls
                   ActionSetAll -> allgls
                   ActionSet -> filter (fn allgls) gls
                   ActionAdd -> nub $ selgls ++ filter (fn allgls) gls
          nwelm = case gls_axm of
                   ChangeGoals -> Element (st {selectedGoals = gls'}) nb
                   ChangeAxioms -> Element (st {includedAxioms = gls'}) nb
          hchg = case gls_axm of
                   ChangeGoals -> GoalsChange (selectedGoals st) nb
                   ChangeAxioms -> AxiomsChange (includedAxioms st) nb
       in parseElements action gls gls_axm ll (nwelm : acc1, hchg : acc2)

{- | A general function that implements the actions of setting,
   adding or deleting goals or axioms from the selection list -}
cGoalsAxmGeneral :: CmdlListAction -> CmdlGoalAxiom ->
                    String -> CmdlState
                 -> IO CmdlState
cGoalsAxmGeneral action gls_axm input state
 = case i_state $ intState state of
    Nothing -> return $ genMsgAndCode "Nothing selected" 1 state
    Just pS ->
     case elements pS of
      [] -> return $ genMsgAndCode "Nothing selected" 1 state
      ls ->
       do
        let gls = words input
        let (ls', hst) = parseElements action gls
                           gls_axm
                           ls ([], [])
        return $ add2hist [ListChange hst] $
                    state {
                      intState = (intState state) {
                        i_state = Just pS {
                                         elements = ls'
                                         }
                             }
                     }

cDoLoop ::
        ProveCmdType
        -> CmdlState
        -> IO CmdlState
cDoLoop proveCmdType state
 = case i_state $ intState state of
    Nothing -> return $ genMsgAndCode "Nothing selected" 1 state
    Just pS ->
        case elements pS of
         [] -> return $ genMsgAndCode "Nothing selected" 1 state
         ls ->
           do
            -- create initial mVars to comunicate
            miSt <- newMVar $ intState state
            mSt <- newMVar Nothing
            mThr <- newMVar Nothing
            mW <- newEmptyMVar
            -- fork
            thrID <- forkIO (doLoop miSt mThr mSt mW ls proveCmdType)
            -- install the handler that waits for SIG_INT
#ifdef UNIX
            oldHandler <- installHandler sigINT (Catch $
                     sigIntHandler mThr miSt mSt thrID mW (i_ln pS)
                                  ) Nothing
#endif
            -- block and wait for answers
            answ <- takeMVar mW
#ifdef UNIX
            installHandler sigINT oldHandler Nothing
#endif
            let nwpS = fromMaybe pS (i_state answ)
                nwls = concatMap (\ (Element _ x) -> selectANode x nwpS) ls
                hst = concatMap (\ (Element stt x) ->
                                 [ AxiomsChange (includedAxioms stt) x
                                 , GoalsChange (selectedGoals stt) x ]) ls
            return $ add2hist [ListChange hst] $
                       state { intState = answ {
                         i_state = Just $ nwpS { elements = nwls }}}

{- | Proves only selected goals from all nodes using selected
   axioms -}
cProve :: CmdlState -> IO CmdlState
cProve = cDoLoop Prove

cDisprove :: CmdlState -> IO CmdlState
cDisprove = cDoLoop Disprove

{- | Proves all goals in the nodes selected using all axioms and
   theorems -}
cProveAll :: CmdlState -> IO CmdlState
cProveAll state
 = case i_state $ intState state of
    Nothing -> return $ genMsgAndCode "Nothing selected" 1 state
    Just pS ->
        case elements pS of
         [] -> return $ genMsgAndCode "Nothing selected" 1 state
         ls ->
            let ls' = map (\ (Element st nb) ->
                               Element (resetSelection st) nb) ls
                nwSt = add2hist [ListChange [NodesChange $ elements pS]] $
                      state {
                       intState = (intState state) {
                         i_state = Just $ pS { elements = ls' } } }
            in cProve nwSt

-- | Sets the use theorems flag of the interface
cSetUseThms :: Bool -> CmdlState -> IO CmdlState
cSetUseThms val state
 = case i_state $ intState state of
    Nothing -> return $ genMsgAndCode "Nothing selected" 1 state
    Just pS ->
      return $ add2hist [UseThmChange $ useTheorems pS] $
          state {
           intState = (intState state) {
             i_state = Just pS {
                             useTheorems = val } } }

cShowOutput :: Bool -> CmdlState -> IO CmdlState
cShowOutput b state =
  case i_state $ intState state of
    Nothing -> return $ genMsgAndCode "Nothing selected" 1 state
    Just pS -> return $ add2hist [ChShowOutput $ showOutput pS] $
       state {
                intState = (intState state) {
                  i_state = Just pS {
                                  showOutput = b } } }

-- | Sets the save2File value to either true or false
cSetSave2File :: Bool -> CmdlState -> IO CmdlState
cSetSave2File val state
 = case i_state $ intState state of
    Nothing -> return $ genMsgAndCode "Nothing selected" 1 state
    Just ps ->
      return $ add2hist [Save2FileChange $ save2file ps] $
          state {
            intState = (intState state) {
             i_state = Just ps { save2file = val } } }


{- | The function is called everytime when the input could
   not be parsed as a command -}
cNotACommand :: String -> CmdlState -> IO CmdlState
cNotACommand input state
 = case input of
     -- if input line is empty do nothing
     [] -> return state
     -- anything else see if it is in a blocl of command
     s ->
      case i_state $ intState state of
        Nothing -> return $ genMsgAndCode ("Error on input line :" ++ s) 1 state
        Just pS ->
          if loadScript pS
            then
             do
              let olds = script pS
                  oldextOpts = tsExtraOpts olds
              let nwSt = state {
                          intState = (intState state) {
                           i_state = Just pS {
                             script = olds { tsExtraOpts = s : oldextOpts }
                             } } }
              return $ add2hist [ScriptChange $ script pS] nwSt
            else return $ genMsgAndCode ("Error on input line :" ++ s) 1 state

-- | Function to signal the interface that the script has ended
cEndScript :: CmdlState -> IO CmdlState
cEndScript state
 = case i_state $ intState state of
    Nothing -> return $ genMsgAndCode "Nothing selected" 1 state
    Just ps ->
     if loadScript ps
       then
         do
          let nwSt = state {
                      intState = (intState state) {
                       i_state = Just ps {
                         loadScript = False } } }
          return $ add2hist [LoadScriptChange $ loadScript ps] nwSt
       else return $ genMsgAndCode "No previous call of begin-script" 1 state

{- | Function to signal the interface that a scrips starts so it should
   not try to parse the input -}
cStartScript :: CmdlState -> IO CmdlState
cStartScript state
 = case i_state $ intState state of
     Nothing -> return $ genMsgAndCode "Nothing selected" 1 state
     Just ps ->
      return $ add2hist [LoadScriptChange $ loadScript ps] $
              state {
                intState = (intState state) {
                  i_state = Just ps {
                                 loadScript = True } } }

-- sets a time limit
cTimeLimit :: String -> CmdlState -> IO CmdlState
cTimeLimit input state
 = case i_state $ intState state of
    Nothing -> return $ genMsgAndCode "Nothing selected" 1 state
    Just ps ->
     if checkIntString $ trim input
       then
        do
         let inpVal = read $ trim input
         let oldS = script ps
         return $ add2hist [ScriptChange $ script ps] $
               state {
                 intState = (intState state) {
                  i_state = Just ps {
                              script = oldS { tsTimeLimit = inpVal } } } }
       else return $ genMsgAndCode "Please insert a number of seconds" 1 state
