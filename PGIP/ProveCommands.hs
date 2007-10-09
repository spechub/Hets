{- |
Module      :$Header$
Description : CMDL interface commands
Copyright   : uni-bremen and DFKI
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.ProveCommands contains all commands
related to prove mode
-}

module PGIP.ProveCommands
       ( shellTranslate
       , shellProver
       , shellProveAll
       , shellProve
       , shellSelectAxms
       , shellSelectGoals
       , shellSetAxmsAll
       , shellSetGoalsAll
       , shellUnselectAxms
       , shellUnselectGoals
       , shellUnselectAxmsAll
       , shellUnselectGoalsAll
       , shellAddAxms
       , shellAddGoals
       , shellUseThms
       , shellDontUseThms
       , shellSave2File
       , shellDontSave2File
       , shellEndScript
       , shellBeginScript
       , shellTimeLimit
       , selectANode
       ) where

import System.Console.Shell.ShellMonad

import PGIP.CMDLState
import PGIP.CMDLUtils
import PGIP.CMDLShell
import PGIP.DgCommands

import Static.GTheory
import Static.DevGraph
-- import Static.DGToSpec

import Common.Result
--import Common.DocUtils
--import Common.Doc
import qualified Common.OrderedMap as OMap

import Data.List
import Data.Graph.Inductive.Graph
import qualified Data.Map as Map

import Comorphisms.LogicGraph

import Proofs.EdgeUtils
import Proofs.StatusUtils
import Proofs.AbstractState
-- import Proofs.BatchProcessing

import Logic.Grothendieck
import Logic.Comorphism
import Logic.Logic
import qualified Logic.Prover as P

import Syntax.AS_Library


import Control.Concurrent
import Control.Concurrent.MVar

import System.Posix.Signals
import System.IO

-- apply comorphisms
shellTranslate :: String -> Sh CMDLState ()
shellTranslate
 = shellComWith cTranslate False False "translate"

-- select a prover
shellProver :: String -> Sh CMDLState ()
shellProver
 = shellComWith cProver False False "prover"



-- | select comorphisms
cTranslate::String -> CMDLState -> IO CMDLState
cTranslate input state =
 case proveState state of
  -- nothing selected !
  Nothing ->return state {
                    errorMsg="Nothing selected"
                    }
  Just pS ->
   -- parse the comorphism name
   case lookupComorphism_in_LG $ trim input of
    Result _ Nothing -> return state {
                                errorMsg = "Wrong comorphism name"
                                }
    Result _ (Just cm) ->
     do
      case cComorphism pS of
       -- no comorphism used before
       Nothing ->
        return $ register2history ("translate "++input) $
                 addToHistory (CComorphismChange $ cComorphism pS)
                 state {
                   proveState = Just pS {
                                  cComorphism = Just cm
                                  }
                        }
       Just ocm ->
        return $ register2history ("translate "++input) $
                 addToHistory (CComorphismChange $ cComorphism pS)
                 state {
                    proveState = Just pS {
                                  cComorphism = compComorphism ocm cm
                                  }
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


addToHistory :: UndoRedoElem -> CMDLState -> CMDLState
addToHistory elm state =
 case proveState state of
  Nothing -> state
  Just pS ->
     let hist  = historyList pS
         uhist = fst hist
         rhist = snd hist
     in state {
           proveState = Just pS {
                          historyList = (elm:uhist,rhist)
                          }
              }

-- | select a prover
cProver::String -> CMDLState -> IO CMDLState
cProver input state =
  do
   -- trimed input
   let inp = trim input
   case proveState state of
    Nothing -> return state {
                        errorMsg = "Nothing selected"
                        }
    Just pS ->
     -- check that some theories are selected
     case elements pS of
      [] -> return state {
                errorMsg="Nothing selected"
                }
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
                   Nothing -> return state {
                                 errorMsg="No applicable prover with"
                                          ++" this name found"
                                 }
                   Just (p,_)->return $ register2history
                                ("prover "++input) $
                                addToHistory (ProverChange $
                                               prover pS)
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
               Nothing -> return state {
                             errorMsg="No applicable prover with"
                                      ++" this name found"
                                      }
               Just (p,nCm@(Comorphism cid))->
                 return $ register2history ("prover " ++ input) $
                         addToHistory (ProverChange $ prover pS)
                         state {
                             errorMsg="Prover can't be used with the "
                                ++"comorphism selected using translate"
                                ++" command. Using comorphism : "
                                ++ language_name cid
                             , proveState = Just pS {
                                             cComorphism=Just nCm
                                             ,prover = Just p
                                             }
                               }
            Just (p,_) -> return $ register2history ("prover "++input)
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
              CMDLProofAbstractState->
              -- selected prover, if non one will be automatically
              -- selected
              Maybe G_prover ->
              -- selected comorphism, if non one will be automatically
              -- selected
              Maybe AnyComorphism ->
              MVar (Maybe ThreadId) ->
              MVar (Maybe CMDLProofAbstractState)  ->
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
                  MVar  (Maybe CMDLProofAbstractState) ->
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
              -> CMDLProofAbstractState
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
           (_,oldContents) =
                labNode' (safeContextDG "PGIP.ProveCommands"
                          dGraph node)
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
                 MVar (Maybe CMDLProofAbstractState) ->
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
             MVar (Maybe CMDLProofAbstractState)  ->
             MVar LibEnv ->
             CMDLProveState ->
             CMDLDevGraphState ->
             [CMDLProofAbstractState] ->
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

parseElements :: ActionType -> [String] -> GoalAxm
                 -> [CMDLProofAbstractState]
                 -> ([CMDLProofAbstractState],[ProofStatusChange])
                 -> ([CMDLProofAbstractState],[ProofStatusChange])
parseElements action gls gls_axm elems (acc1,acc2)
 = case elems of
    [] -> (acc1,acc2)
    (Element st nb):ll ->
      let allgls = case gls_axm of
                    TypeGoal -> OMap.keys $ goalMap st
                    TypeAxm  -> case theory st of
                                 G_theory _ _ _ aMap _ ->
                                  OMap.keys aMap
          selgls = case gls_axm of
                    TypeGoal -> selectedGoals st
                    TypeAxm  -> includedAxioms st
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
cGoalsAxmGeneral :: String -> ActionType -> GoalAxm ->
                    String ->CMDLState
                 -> IO CMDLState
cGoalsAxmGeneral name action gls_axm input state
 = case proveState state of
    Nothing -> return state {errorMsg = "Nothing selected"}
    Just pS ->
     case elements pS of
      [] -> return state{errorMsg = "Nothing selected"}
      ls ->
       do
        let gls = words input
        let (ls',hist) = parseElements action gls
                           gls_axm
                           ls ([],[])
        return $ register2history (name++input) $
                 addToHistory (ListChange hist)
                    state {proveState = Just pS {
                                         elements = ls'
                                         }
                     }

-- | Proves only selected goals from all nodes using selected
-- axioms
cProve::String -> CMDLState-> IO CMDLState
cProve name state
 = case proveState state of
    Nothing -> return state {errorMsg = "Nothing selected"}
    Just pS ->
     case devGraphState state of
      Nothing -> return state{errorMsg="No library loaded"}
      Just dgS ->
       do
        case elements pS of
         [] -> return state{errorMsg="Nothing selected"}
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
            return $ register2history name $
                     addToHistory (ProveChange (libEnv dgS) hist)
                         state {
                            devGraphState = Just nwDgS
                           ,proveState = Just pS {
                                               elements = nwls
                                               }
                          }

-- | Proves all goals in the nodes selected using all axioms and
-- theorems
cProveAll::CMDLState ->IO CMDLState
cProveAll state
 = case proveState state of
    Nothing -> return state {errorMsg = "Nothing selected" }
    Just pS ->
       do
        case elements pS of
         [] -> return state{errorMsg="Nothing selected"}
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
            cProve "prove-all " nwSt

-- | Sets the use theorems flag of the interface
cSetUseThms :: String->Bool -> CMDLState -> IO CMDLState
cSetUseThms name val state
 = case proveState state of
    Nothing -> return state {errorMsg = "Norhing selected"}
    Just pS ->
     do
      return $ register2history name $
         addToHistory (UseThmChange $ useTheorems pS)
          state {
         proveState = Just pS {
                             useTheorems = val
                             }
                   }

-- | Sets the save2File value to either true or false
cSetSave2File :: String->Bool -> CMDLState -> IO CMDLState
cSetSave2File name val state
 = case proveState state of
    Nothing -> return state {errorMsg = "Nothing selected"}
    Just ps ->
     do
      return $ register2history name $
        addToHistory (Save2FileChange $ save2file ps)
          state {
            proveState = Just ps {
                            save2file = val
                            }
                   }

-- | Function to signal the interface that the script has ended
cEndScript :: CMDLState -> IO CMDLState
cEndScript state
 = case proveState state of
    Nothing -> return state {errorMsg = "Nothing selected"}
    Just ps ->
     case loadScript ps of
      False -> return state {errorMsg = "No previous call of "
                                       ++ "begin-script"
                               }
      True ->
       do
        let nwSt= state {
                      proveState = Just ps {
                            loadScript = False
                            }
                   }
        return $ register2history "end-script " $
               addToHistory (LoadScriptChange $ loadScript ps) nwSt

-- | Function to signal the interface that a scrips starts so it should
-- not try to parse the input
cStartScript :: CMDLState-> IO CMDLState
cStartScript state
 = do
    case proveState state of
     Nothing -> return state {errorMsg="Nothing selected"}
     Just ps ->
      return $ register2history "begin-script" $
             addToHistory (LoadScriptChange $ loadScript ps)
            $ addToHistory (ScriptChange $ script ps)
              state {
                  proveState = Just ps {
                                     loadScript = True
                                     }
                   }


cTimeLimit :: String -> CMDLState-> IO CMDLState
cTimeLimit input state
 = case proveState state of
    Nothing -> return state {errorMsg="Nothing selected"}
    Just ps ->
     case checkIntString input of
       False -> return state
                       {errorMsg="Please insert a number of seconds"}
       True ->
        do
        case isInfixOf "Time Limit: " $ script ps of
         True -> return state {errorMsg="Time limit already set"}
         False->
           return $ register2history ("set time-limit "++input)
              $ addToHistory (ScriptChange $ script ps)
               state {
                 proveState = Just ps {
                                 script = ("Time Limit: " ++ input
                                            ++"\n"++ (script ps))
                                     }
                      }



shellTimeLimit :: String -> Sh CMDLState ()
shellTimeLimit
 = shellComWith cTimeLimit False False "set time-limit"

shellSelectAxms :: String -> Sh CMDLState ()
shellSelectAxms
 = shellComWith (cGoalsAxmGeneral  "set axioms " ActionSet TypeAxm)
                False False "set axioms"

shellSetAxmsAll :: Sh CMDLState ()
shellSetAxmsAll
 = shellComWithout (cGoalsAxmGeneral "set-all axioms "
                      ActionSetAll TypeAxm "")
                   False False "set-all axioms"

shellUnselectAxms :: String -> Sh CMDLState ()
shellUnselectAxms
 = shellComWith (cGoalsAxmGeneral "del axioms " ActionDel TypeAxm)
                False False "del axioms"

shellUnselectAxmsAll :: Sh CMDLState ()
shellUnselectAxmsAll
 = shellComWithout (cGoalsAxmGeneral  "del-all axioms "
                    ActionDelAll TypeAxm "")
                   False False "del-all axioms"

shellAddAxms :: String -> Sh CMDLState ()
shellAddAxms
 = shellComWith (cGoalsAxmGeneral "add axioms" ActionAdd TypeAxm )
                 False False "add axioms"


shellSelectGoals :: String -> Sh CMDLState ()
shellSelectGoals
 = shellComWith (cGoalsAxmGeneral "set goals " ActionSet TypeGoal )
                   False False "set goals"

shellSetGoalsAll :: Sh CMDLState ()
shellSetGoalsAll
 = shellComWithout (cGoalsAxmGeneral "set-all goals "
                    ActionSetAll TypeGoal "")
                    False False "set-all goals"

shellUnselectGoals:: String -> Sh CMDLState ()
shellUnselectGoals
 = shellComWith (cGoalsAxmGeneral "del goals " ActionDel TypeGoal )
                False False "del goals"

shellUnselectGoalsAll :: Sh CMDLState ()
shellUnselectGoalsAll
 = shellComWithout (cGoalsAxmGeneral "del-all goals " ActionDelAll
                    TypeGoal "") False False "del-all goals"

shellAddGoals :: String -> Sh CMDLState ()
shellAddGoals
 = shellComWith (cGoalsAxmGeneral "add goals " ActionAdd TypeGoal)
                   False False "add goals"

shellUseThms :: Sh CMDLState ()
shellUseThms
 = shellComWithout (cSetUseThms "set include-theorems true" True)
                     False False "set include-theorems true"

shellDontUseThms :: Sh CMDLState ()
shellDontUseThms
 = shellComWithout (cSetUseThms "set include-theorems false" False)
                     False False "set include-theorems false"

shellSave2File :: Sh CMDLState ()
shellSave2File
 = shellComWithout (cSetSave2File "set save-prove-to-file true" True)
                     False False "set save-prove-to-file true"

shellDontSave2File :: Sh CMDLState ()
shellDontSave2File
 = shellComWithout (cSetSave2File "set save-prove-to-file false" False)
                      False False "set save-prove-to-file false"


shellBeginScript :: Sh CMDLState ()
shellBeginScript
 = shellComWithout cStartScript False False "begin-script"


shellProve :: Sh CMDLState ()
shellProve
 = shellComWithout (cProve "prove ") False False "prove"


shellProveAll :: Sh CMDLState ()
shellProveAll
 = shellComWithout cProveAll False False "prove-all"

shellEndScript :: Sh CMDLState ()
shellEndScript
 = shellComWithout cEndScript False True "end-script"


