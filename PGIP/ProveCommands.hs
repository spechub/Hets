{- |
Module      :$Header$
Description : CMDL interface commands
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.ProveCommands contains all commands
related to prove mode
-}

module PGIP.ProveCommands
       ( cTranslate
       , cDropTranslations
       , cProver
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

import Static.GTheory
import Static.DevGraph

import Common.Result
import qualified Common.OrderedMap as OMap

import Data.List
import qualified Data.Map as Map

import Comorphisms.LogicGraph

import Proofs.EdgeUtils
import Proofs.StatusUtils
import Proofs.AbstractState

import Logic.Grothendieck
import Logic.Comorphism
import Logic.Logic
import qualified Logic.Prover as P

import Syntax.AS_Library


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
     Just _ -> return state {
                          proveState = Just $ pS {
                                         cComorphism = Nothing },
                          prompter = (prompter state)\\"*"
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
       -- no comorphism used before
       Nothing ->
        return $ genMessage [] "Adding comorphism" $
                 addToHistory (CComorphismChange $ cComorphism pS)
                 state {
                   proveState = Just pS {
                                  cComorphism = Just cm
                                  },
                   prompter = (reverse $ safeTail $ safeTail $ reverse $
                                prompter state) ++ "*> "
                        }
       Just ocm ->
        case compComorphism ocm cm of
         Nothing ->
           return $ genErrorMsg "Can not compose comorphisms" state {
                      proveState = Just pS {
                                  cComorphism = Just ocm
                                  }
                      }
         Just smth ->
           return $ genMessage [] "Composing comorphisms"
                  $ addToHistory (CComorphismChange $ cComorphism pS)
                    state {
                      proveState = Just pS {
                                  cComorphism = Just smth
                                  },
                      prompter = (reverse $ safeTail $ safeTail $ reverse $
                                   prompter state) ++ "*> "
                      }

getProversCMDLautomatic::[AnyComorphism]->[(G_prover,AnyComorphism)]
getProversCMDLautomatic = foldl addProvers []
 where addProvers acc cm =
        case cm of
         Comorphism cid -> acc ++
            foldl (\ l p ->
                         if P.hasProverKind
                            P.ProveCMDLautomatic p
                         then (G_prover (targetLogic cid)
                               p,cm):l
                         else l)
                       []
                       (provers $ targetLogic cid)


addToHistory :: CMDL_UndoRedoElem -> CMDL_State -> CMDL_State
addToHistory elm state =
 case proveState state of
  Nothing -> state
  Just _ ->
     let oH  = history state
         oH' = tail $ undoInstances oH
         hist  = head $ undoInstances oH
         uhist = fst hist
         rhist = snd hist
     in state {
           history = oH {
                      undoInstances = (elm:uhist,rhist):oH',
                      redoInstances = []
                      }
          }

-- | select a prover
cProver::String -> CMDL_State -> IO CMDL_State
cProver input state =
  do
   -- trimed input
   let inp = trim input
   case proveState state of
    Nothing -> return $ genErrorMsg "Nothing selected" state
    Just pS ->
     -- check that some theories are selected
     case elements pS of
      [] -> return $ genErrorMsg "Nothing selected" state
      (Element z _):_ ->
        -- see if any comorphism was used
       case cComorphism pS of
       -- if none use the theory  of the first selected node
       -- to find possible comorphisms
       Nothing-> case find (\(y,_)->
                                (getPName y)==inp) $
                        getProversCMDLautomatic $
                        findComorphismPaths logicGraph $
                        sublogicOfTh $ theory z of
                   Nothing -> return $genErrorMsg ("No applicable prover with"
                                                ++" this name found") state
                   Just (p,_)->return $ addToHistory(ProverChange $prover pS)
                                   state {
                                      proveState=Just pS {prover = Just p }
                                      }
       -- if yes,  use the comorphism to find a list
       -- of provers
       Just x ->
         case find (\(y,_)-> (getPName y)==inp)
                   $ getProversCMDLautomatic [x] of
            Nothing ->
             case find (\(y,_) ->
                             (getPName y)==inp) $
                      getProversCMDLautomatic $
                      findComorphismPaths logicGraph $
                      sublogicOfTh $ theory z of
               Nothing -> return $ genErrorMsg ("No applicable prover with"
                                          ++" this name found") state
               Just (p,nCm@(Comorphism cid))->
                 return $ addToHistory (ProverChange $ prover pS)
                     $ genMessage ("Prover can't be used with the "
                            ++"comorphism selected using translate"
                            ++" command. Using comorphism : "
                            ++ language_name cid) []
                            state {
                              proveState = Just pS {
                                             cComorphism=Just nCm
                                             ,prover = Just p
                                             }
                               }
            Just (p,_) -> return
                              $ addToHistory (ProverChange $ prover pS)
                                state {
                                  proveState = Just pS {
                                              prover = Just p
                                         }
                              }


-- | Given a proofstatus the function does the actual call of the
-- prover
proveNode ::
              --use theorems is subsequent proofs
              Bool ->
              -- save problem file for each goal
              Bool ->
              -- Tactic script
              String ->
              -- proofState of the node that needs proving
              -- all theorems, goals and axioms should have
              -- been selected before,but the theory should have
              -- not beed recomputed
              CMDL_ProofAbstractState->
              -- selected prover, if non one will be automatically
              -- selected
              Maybe G_prover ->
              -- selected comorphism, if non one will be automatically
              -- selected
              Maybe AnyComorphism ->
              MVar (Maybe ThreadId) ->
              MVar (Maybe CMDL_ProofAbstractState)  ->
              MVar LibEnv ->
              LIB_NAME ->
              -- returns an error message if anything happen
               IO String
proveNode useTh save2File sTxt ndpf mp mcm mThr mSt mlbE libname
 =case ndpf of
   Element pf_st nd ->
    do
    -- recompute the theory (to make effective the selected axioms,
    -- goals)
    st <- recalculateSublogicAndSelectedTheory pf_st
    -- compute a prover,comorphism pair to be used in preparing
    -- the theory
    p_cm@(_,acm)
        <-case mcm of
           Nothing -> lookupKnownProver st P.ProveCMDLautomatic
           Just cm' ->
            case mp of
             Nothing-> lookupKnownProver st P.ProveCMDLautomatic
             Just p' -> return (p',cm')
    -- try to prepare the theory
    prep <- case prepareForProving st p_cm of
             Result _ Nothing ->
               do
                p_cm'@(_,acm') <-
                          lookupKnownProver st P.ProveCMDLautomatic
                return $ case prepareForProving st p_cm' of
                          Result _ Nothing -> Nothing
                          Result _ (Just sm)-> Just (sm,acm')
             Result _ (Just sm) -> return $ Just (sm,acm)
    case prep of
     -- theory could not be computed
     Nothing -> do
                 return "No suitable prover and comorphism found"
     Just (G_theory_with_prover lid1 th p, cmp)->
      case P.proveCMDLautomaticBatch p of
         Nothing -> do
                     return "Error obtaining the prover"
         Just fn ->
          do
          -- mVar to poll the prover for results
          answ <- newMVar (return [])
          let st' = st { proverRunning= True}
          -- store initial input of the prover
          swapMVar mSt $ Just $ Element st' nd
          {- putStrLn ((theoryName st)++"\n"++
                    (showDoc sign "") ++
                    show (vsep (map (print_named lid1)
                                        $ P.toNamedList sens))) -}
          case selectedGoals st' of
           [] -> return "No goals selected. Nothing to prove"
           _ ->
            do
             tmp <-fn useTh
                      save2File
                      answ
                      (theoryName st)
                      (P.Tactic_script sTxt)
                      th
             swapMVar mThr $ Just $ fst tmp
             pollForResults lid1 cmp (snd tmp) answ mSt []
             swapMVar mThr $ Nothing
             lbEnv  <- readMVar mlbE
             state <- readMVar mSt
             case state of
              Nothing -> return []
              Just state' ->
               do
                lbEnv' <- addResults lbEnv libname state'
                swapMVar mSt  Nothing
                swapMVar mlbE lbEnv'
                return []


pollForResults :: (Logic lid sublogics basic_spec sentence
                       symb_items symb_map_items
                       sign morphism symbol raw_symbol proof_tree) =>
                  lid ->
                  AnyComorphism ->
                  MVar () ->
                  MVar (Result [P.Proof_status proof_tree]) ->
                  MVar  (Maybe CMDL_ProofAbstractState) ->
                  [P.Proof_status proof_tree] ->
                  IO ()
pollForResults lid acm mStop mData mState done
 =do
  let toPrint ls=map(\x->let txt = "Goal "++(P.goalName x)++" is "
                         in case P.goalStatus x of
                             P.Open     ->txt++"still open."
                             P.Disproved->txt++"disproved."
                             P.Proved _ ->txt++"proved.") ls
  d <- takeMVar mData
  case d of
    Result _ Nothing ->
     do
      tmp <- tryTakeMVar mStop
      case tmp of
       Just () ->
                  do
                  t <- readMVar mData
                  case t of
                    Result _ (Just _) ->
                       do
                        putMVar mStop ()
                        pollForResults lid acm mStop mData mState done
                    Result _ Nothing ->
                        return ()
       Nothing -> pollForResults lid acm mStop mData mState done
    Result _ (Just d') ->
     do
      let d'' = nub d'
          l   = d'' \\ done
          ls = toPrint l
      smth <- readMVar mState
      case smth of
       Nothing ->
        do
         tmp <- tryTakeMVar mStop
         case tmp of
          Just () -> return ()
          Nothing -> pollForResults lid acm mStop mData mState done
       Just  (Element st node) ->
        do
         putStrLn $ prettyPrintList ls
         swapMVar mState $ Just $ Element (markProved acm lid l st) node
         tmp <- tryTakeMVar mStop
         case tmp of
          Just () -> return ()
          Nothing -> pollForResults lid acm mStop mData mState
                                                     (done++l)



-- | inserts the results of the proof in the development graph
addResults ::    LibEnv
              -> LIB_NAME
              -> CMDL_ProofAbstractState
              -> IO LibEnv
addResults lbEnv libname ndps
 =case ndps of
   Element ps' node ->
    do
    -- inspired from Proofs/InferBasic.hs
    -- and GUI/ProofManagement.hs
    let ps'' = ps' {
                    proverRunning = False }
    case theory ps'' of
     G_theory lidT sigT indT sensT _ ->
      do
       gMap <-coerceThSens (logicId ps'') lidT
                  "ProveCommands last coerce"
                  (goalMap ps'')
       let nwTh = G_theory lidT sigT indT (Map.union sensT gMap) 0
           dGraph = lookupDGraph libname lbEnv
           oldContents = labDG dGraph node
           newContents = oldContents {dgn_theory = nwTh}
           (nextDGraph,changes) =
                  updateWithOneChange (SetNodeLab
                                        (error "addResults")
                                           (node,newContents)) dGraph []
           rules = []
           nextHistoryElem = (rules, changes)
       return $ mkResultProofStatus libname lbEnv nextDGraph
                  nextHistoryElem


-- | Signal handler that stops the prover from running
-- when SIGINT is send
sigIntHandler :: MVar (Maybe ThreadId) ->
                 MVar LibEnv ->
                 MVar (Maybe CMDL_ProofAbstractState) ->
                 ThreadId ->
                 MVar LibEnv ->
                 LIB_NAME ->
                 IO ()
sigIntHandler mthr mlbE mSt thr mOut libname
 = do
   -- print a message
   -- ? shellputStr ! should be used !
   putStrLn "Prover stopped."
   -- check if the prover is runnig
   tmp <- readMVar mthr
   case tmp of
     Nothing -> return ()
     Just sm -> killThread sm
   -- kill the prove/prove-all thread
   killThread thr
   -- update LibEnv with intermidiar results !?
   lbEnv <- readMVar mlbE
   st <- readMVar mSt
   case st of
    Nothing ->
      do
       putMVar mOut lbEnv
       return ()
    Just st' ->
      do
       lbEnv' <- addResults lbEnv libname st'
        -- add to the output mvar results until now
       putMVar mOut lbEnv'
       return ()

proveLoop :: MVar LibEnv ->
             MVar (Maybe ThreadId) ->
             MVar (Maybe CMDL_ProofAbstractState)  ->
             MVar LibEnv ->
             CMDL_ProveState ->
             CMDL_DevGraphState ->
             [CMDL_ProofAbstractState] ->
             IO ()
proveLoop mlbE mThr mSt mOut pS pDgS ls
 = case ls of
   -- we are done
    [] -> do
           nwLbEnv <- readMVar mlbE
           putMVar mOut nwLbEnv
           return ()
    x: l ->
          do
           let nodeName x' = case x' of
                              Element _ t -> case find(\(n,_)-> n==t)
                                                  $ getAllNodes pDgS of
                                               Nothing -> "Unkown node"
                                               Just (_,ll) ->
                                                 getDGNodeName ll
           putStrLn ("Analyzing node " ++ nodeName x)
           err <- proveNode (useTheorems pS)
                            (save2file pS)
                            (script pS)
                            x
                            (prover pS)
                            (cComorphism pS)
                            mThr
                            mSt
                            mlbE
                            (ln pDgS)
           case err of
            [] -> proveLoop mlbE mThr mSt mOut pS pDgS l
            _  -> do
                  putStrLn err
                  proveLoop mlbE mThr mSt mOut pS pDgS l

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
        case elements pS of
         [] -> return $ genErrorMsg "Nothing selected" state
         ls ->
           do
            --create inital mVars to comunicate
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


cTimeLimit :: String -> CMDL_State-> IO CMDL_State
cTimeLimit input state
 = case proveState state of
    Nothing -> return $ genErrorMsg "Nothing selected" state
    Just ps ->
     case checkIntString input of
       False -> return $ genErrorMsg "Please insert a number of seconds" state
       True ->
        do
        case isInfixOf "Time Limit: " $ script ps of
         True -> return $ genErrorMsg "Time limit already set" state
         False->
           return $ addToHistory (ScriptChange $ script ps)
               state {
                 proveState = Just ps {
                                 script = ("Time Limit: " ++ input
                                            ++"\n"++ (script ps))
                                     }
                      }


