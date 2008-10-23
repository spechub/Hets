{- |
Module      : $Header$
Description : CMDL interface commands
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.ProveCommands contains all commands (except prove\/consistency check)
related to prove mode
-}

module PGIP.ProveCommands
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

import PGIP.DataTypes
import PGIP.DataTypesUtils
import PGIP.Utils
import PGIP.DgCommands
import PGIP.ProveConsistency

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

-- | Drops any seleceted comorphism
cDropTranslations :: CMDL_State -> IO CMDL_State
cDropTranslations state =
 case proveState state of
   Nothing -> return $ genErrorMsg "Nothing selected" state
   Just pS ->
    case cComorphism pS of
     Nothing -> return state
     Just _ -> return 
        state {
          proveState = Just $ pS {
                cComorphism = getIdComorphism $ elements pS  },
                prompter = (prompter state) {
                                             selectedTranslations = []}
                }


-- | select comorphisms
cTranslate::String -> CMDL_State -> IO CMDL_State
cTranslate input state =
 case proveState state of
  -- nothing selected !
  Nothing ->return $ genErrorMsg "Nothing selected" state
  Just pS ->
   -- parse the comorphism name
   case lookupComorphism_in_LG $ trim input of
    Result _ Nothing -> return $ genErrorMsg "Wrong comorphism name" state
    Result _ (Just cm) ->
     do
      case cComorphism pS of
       -- when selecting some theory the Id comorphism is automatically
       -- generated
       Nothing -> return $ genErrorMsg "No theory selected" state
       Just ocm ->
        case compComorphism ocm cm of 
            Nothing ->
             return $ genErrorMsg "Can not add comorphism" state {
                       proveState = Just pS {
                                              cComorphism = Just ocm
                                    }
                          }
            Just smth ->
              return $ genMessage [] "Adding comorphism"
                     $ addToHistory (CComorphismChange $ cComorphism pS)
                      state {
                        proveState = Just pS {
                                     cComorphism = Just smth
                                     },
                        prompter = (prompter state) {
                                    selectedTranslations=(selectedTranslations
                                        $ prompter state) ++ "*" }
                          }

        
--      case cComorphism pS of
--      -- no comorphism used before
--       Nothing ->
--        return $ genMessage [] "Adding comorphism" $
--                 addToHistory (CComorphismChange $ cComorphism pS)
--                 state {
--                   proveState = Just pS {
--                                  cComorphism = Just cm
--                                  },
--                   prompter = (prompter state) {
--                                 selectedTranslations = "*" }
--                        }
--       Just ocm ->
--        case compComorphism ocm cm of

parseElements :: CMDL_ListAction -> [String] -> CMDL_GoalAxiom
                 -> [CMDL_ProofAbstractState]
                 -> ([CMDL_ProofAbstractState],[CMDL_ListChange])
                 -> ([CMDL_ProofAbstractState],[CMDL_ListChange])
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
          nwelm = Element (st { selectedGoals = gls' }) nb
       in parseElements action gls gls_axm ll (nwelm:acc1,
                          (GoalsChange (selectedGoals st) nb):acc2)

-- | A general function that implements the actions of setting,
-- adding or deleting goals or axioms from the selection list
cGoalsAxmGeneral :: CMDL_ListAction -> CMDL_GoalAxiom ->
                    String ->CMDL_State
                 -> IO CMDL_State
cGoalsAxmGeneral action gls_axm input state
 = case proveState state of
    Nothing -> return $ genErrorMsg "Nothing selected" state
    Just pS ->
     case elements pS of
      [] -> return $ genErrorMsg "Nothing selected" state
      ls ->
       do
        let gls = words input
        let (ls',hist) = parseElements action gls
                           gls_axm
                           ls ([],[])
        return $ addToHistory (ListChange hist)
                    state {proveState = Just pS {
                                         elements = ls'
                                         }
                     }

-- | Proves only selected goals from all nodes using selected
-- axioms
cProve:: CMDL_State-> IO CMDL_State
cProve state
 = case proveState state of
    Nothing -> return $ genErrorMsg "Nothing selected" state
    Just pS ->
     case devGraphState state of
      Nothing -> return $ genErrorMsg "No library loaded" state
      Just dgS ->
       do
        putStrLn $ script pS 
        case elements pS of
         [] -> return $ genErrorMsg "Nothing selected" state
         ls ->
           do
            --create initial mVars to comunicate
            mlbEnv <- newMVar $ libEnv dgS
            mSt    <- newMVar Nothing
            mThr   <- newMVar Nothing
            mW     <- newEmptyMVar
            -- fork
            thrID <- forkIO(proveLoop mlbEnv mThr mSt mW pS dgS ls)
            -- install the handler that waits for SIG_INT
            installHandler sigINT (Catch $
                     sigIntHandler mThr mlbEnv mSt thrID mW (ln dgS)
                                  ) Nothing
            -- block and wait for answers
            answ <- takeMVar mW
            let nwDgS = dgS {
                             libEnv = answ
                             }
            let nwls=concatMap(\(Element _ x) ->
                                              selectANode x nwDgS) ls
                hist=concatMap(\(Element stt x)  ->
                                 (AxiomsChange (includedAxioms stt) x):
                                 (GoalsChange (selectedGoals stt) x):
                                   []) ls
            return $ addToHistory (ProveChange (libEnv dgS) hist)
                         state {
                            devGraphState = Just nwDgS
                           ,proveState = Just pS {
                                               elements = nwls
                                               }
                          }

-- | Proves all goals in the nodes selected using all axioms and
-- theorems
cProveAll::CMDL_State ->IO CMDL_State
cProveAll state
 = case proveState state of
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
            let nwSt = state {
                          proveState = Just pS {
                                        elements = ls'
                                          }
                              }
            cProve nwSt

-- | Sets the use theorems flag of the interface
cSetUseThms :: Bool -> CMDL_State -> IO CMDL_State
cSetUseThms val state
 = case proveState state of
    Nothing -> return $ genErrorMsg "Norhing selected" state
    Just pS ->
     do
      return $ addToHistory (UseThmChange $ useTheorems pS)
          state {
         proveState = Just pS {
                             useTheorems = val
                             }
                   }

-- | Sets the save2File value to either true or false
cSetSave2File :: Bool -> CMDL_State -> IO CMDL_State
cSetSave2File val state
 = case proveState state of
    Nothing -> return $ genErrorMsg "Nothing selected" state
    Just ps ->
     do
      return $ addToHistory (Save2FileChange $ save2file ps)
          state {
            proveState = Just ps {
                            save2file = val
                            }
                   }


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
      case proveState state of
        Nothing -> return $ genErrorMsg ("Error on input line :"++s) state
        Just pS ->
          case loadScript pS of
            False -> return$ genErrorMsg ("Error on input line :"++s) state
            True ->
             do
              let nwSt = state {
                          proveState=Just pS{script=((script pS)++s++"\n")}
                          }
              return $ addToHistory (ScriptChange $ script pS) nwSt


-- | Function to signal the interface that the script has ended
cEndScript :: CMDL_State -> IO CMDL_State
cEndScript state
 = case proveState state of
    Nothing -> return $ genErrorMsg "Nothing selected" state
    Just ps ->
     case loadScript ps of
      False -> return $ genErrorMsg "No previous call of begin-script" state
      True ->
       do
        let nwSt= state {
                      proveState = Just ps {
                            loadScript = False
                            }
                   }
        return $ addToHistory (LoadScriptChange $ loadScript ps) nwSt

-- | Function to signal the interface that a scrips starts so it should
-- not try to parse the input
cStartScript :: CMDL_State-> IO CMDL_State
cStartScript state
 = do
    case proveState state of
     Nothing -> return $ genErrorMsg "Nothing selected" state
     Just ps ->
      return $ addToHistory (LoadScriptChange $ loadScript ps)
            $ addToHistory (ScriptChange $ script ps)
              state {
                  proveState = Just ps {
                                     loadScript = True
                                     }
                   }

-- sets a time limit
cTimeLimit :: String -> CMDL_State-> IO CMDL_State
cTimeLimit input state
 = case proveState state of
    Nothing -> return $ genErrorMsg "Nothing selected" state
    Just ps ->
     case checkIntString $ trim input of
       False -> return $ genErrorMsg "Please insert a number of seconds" state
       True ->
        do
        putStrLn input
        case isInfixOf "Time Limit: " $ script ps of
         True -> return $ genErrorMsg "Time limit already set" state
         False->
           return $ addToHistory (ScriptChange $ script ps)
               state {
                 proveState = Just ps {
                                 script = ("Time Limit: " ++ (trim input)
                                            ++"\n"++ (script ps))
                                     }
                      }
