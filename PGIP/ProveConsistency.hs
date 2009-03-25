{- |
Module      :$Header$
Description : CMDL interface commands
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.ProveConsistency contains prove and consistency check command
-}


module PGIP.ProveConsistency
       ( cProver
       , cConsChecker
       , checkNode
       , proveNode
       , proveLoop
       , consCheckLoop
       , sigIntHandler
       ) where


import Interfaces.DataTypes

import PGIP.DataTypes
import PGIP.DataTypesUtils
import PGIP.Utils

import Comorphisms.LogicGraph

import Proofs.EdgeUtils
import Proofs.AbstractState

import Static.GTheory
import Static.DevGraph

import Logic.Grothendieck
import Logic.Comorphism
import Logic.Logic
import qualified Logic.Prover as P

import Common.LibName
import Common.Result

import Data.List
import qualified Data.Map as Map

import Control.Concurrent
import Control.Concurrent.MVar

import System.IO

import Interfaces.GenericATPState

getProversAutomatic :: [AnyComorphism] -> [(G_prover, AnyComorphism)]
getProversAutomatic = foldl addProvers []
 where addProvers acc cm =
        case cm of
         Comorphism cid -> acc ++
             foldl (\ l p ->
                          if P.hasProverKind
                             P.ProveCMDLautomatic p
                          then (G_prover (targetLogic cid)
                             p,cm):l
                          else l) []  (provers $ targetLogic cid)


-- | Select a prover
cProver::String -> CMDL_State ->
                    IO CMDL_State
cProver input state =
  do
   -- trimed input
   inpls <- checkPresenceProvers [(trim input)]
   let inp  = case inpls of
                [] -> "Unknown"
                pnme:_ ->pnme
   case i_state $ intState state of
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
                           getProversAutomatic $ findComorphismPaths
                              logicGraph $ sublogicOfTh $ theory z of
                   Nothing -> return $ genErrorMsg ("No applicable prover with"
                                                ++" this name found") state
                   Just (p,_)-> return $ add2hist [ProverChange$ prover pS]$
                                    state {
                                         intState = (intState state) {
                                            i_state = Just pS {
                                                        prover = Just p
                                              }
                                         }
                                 }
       -- if yes,  use the comorphism to find a list
       -- of provers
       Just x ->
         case find (\(y,_)-> (getPName y)==inp)
                   $ getProversAutomatic [x] of
            Nothing ->
             case find (\(y,_) ->
                             (getPName y)==inp) $
                      getProversAutomatic $
                      findComorphismPaths logicGraph $
                      sublogicOfTh $ theory z of
               Nothing -> return $ genErrorMsg ("No applicable prover with"
                                          ++" this name found") state
               Just (p,nCm@(Comorphism cid))->
                 return $ add2hist [(ProverChange $ prover pS),
                                    (CComorphismChange $ cComorphism pS)]
                     $ genMessage [] ("Warning: Prover can't be used with "
                            ++"the selected comorphism (or the default if "
                            ++"none was selected). Instead the `"
                            ++ (language_name  cid)
                            ++"` comorphism was selected. Current prover is "
                            ++ input)
                            state {
                              intState = (intState state) {
                                i_state = Just pS {
                                             cComorphism=Just nCm
                                             ,prover = Just p
                                             }
                                      }
                               }
            Just (p,_) -> return
                              $ add2hist [ProverChange $ prover pS]
                                state {
                                  intState = (intState state) {
                                    i_state = Just pS {
                                               prover = Just p
                                               }
                                     }
                                  }


-- | Selects a consistency checker
cConsChecker::String -> CMDL_State -> IO CMDL_State
cConsChecker input state =
  do
   --trimed input
   let inp = trim input
   case i_state $ intState state of
    Nothing -> return $ genErrorMsg "Nothing selected" state
    Just pS ->
     --check that some theories are selected
     case elements pS of
      [] -> return $ genErrorMsg "Nothing selected" state
      Element z _ : _ ->
        -- see if any comorphism was used
        case cComorphism pS of
        --if none use the theory of the first selected node
        --to find possible comorphisms
        Nothing -> case find (\(y,_)->
                                  getPName y == inp) $
                             getConsCheckersAutomatic $ findComorphismPaths
                                logicGraph $ sublogicOfTh $ theory z of
                    Nothing -> return $ genErrorMsg ("No applicable "++
                                 "consistency checker with this name found")
                                 state
                    Just (p,_) -> return $ add2hist
                                    [ConsCheckerChange $ consChecker pS]
                                    state {
                                      intState = (intState state) {
                                         i_state = Just pS {
                                             consChecker = Just p }
                                          }
                                      }
        Just x ->
          case find(\(y,_) -> (getPName y) == inp)
                     $ getConsCheckersAutomatic [x] of
           Nothing ->
            case find (\(y,_) ->
                        (getPName y) == inp)$ getConsCheckersAutomatic $
                          findComorphismPaths logicGraph $ sublogicOfTh $
                          theory z of
             Nothing -> return $ genErrorMsg ("No applicable consistency "++
                                 "checker with this name found") state
             Just (p,nCm@(Comorphism cid)) ->
               return $ add2hist [(ConsCheckerChange $ consChecker pS),
                                  (CComorphismChange $ cComorphism pS)]
                  $ genMessage ("Consistency checker can't be used with the "
                      ++"comorphism selected using translate "
                      ++"command. Using comorphism :"
                      ++ language_name cid) []
                      state {
                       intState = (intState state) {
                         i_state = Just pS {
                                    cComorphism = Just nCm,
                                    consChecker = Just p }
                                  }
                          }
           Just (p,_) -> return
                           $ add2hist [ConsCheckerChange $ consChecker pS]
                            $ state {
                            intState = (intState state) {
                              i_state = Just pS{
                                          consChecker = Just p } } }


-- | Given a proofstatus the function does the actual call of the
-- prover for consistency checking
checkNode ::
              --use theorems is subsequent proofs
              Bool ->
              -- save problem file for each goal
              Bool ->
              -- Tactic script
              ATPTactic_script ->
              -- proofState of the node that needs proving
              -- all theorems, goals and axioms should have
              -- been selected before,but the theory should have
              -- not beed recomputed
              Int_NodeInfo ->
              -- node name
              String ->
              -- selected prover, if non one will be automatically
              -- selected
              Maybe G_cons_checker ->
              -- selected comorphism, if non one will be automatically
              -- selected
              Maybe AnyComorphism ->
              MVar (Maybe ThreadId) ->
              MVar (Maybe Int_NodeInfo)  ->
              MVar LibEnv ->
              LIB_NAME ->
              -- returns an error message if anything happens
               IO String
checkNode useTh save2File sTxt ndpf ndnm mp mcm mThr mSt mlbE libname
 =do
   case ndpf of
    Element pf_st nd ->
     do
     -- recompute the theory (to make effective the selected axioms,
     -- goals) !? needed?
     st <- recalculateSublogicAndSelectedTheory pf_st
     -- compute a prover,comorphism pair to be used in preparing
     -- the theory
     p_cm@(_,acm)
        <-case mcm of
           Nothing -> lookupKnownConsChecker st P.ProveCMDLautomatic
           Just cm' ->
            case mp of
             Nothing-> lookupKnownConsChecker st P.ProveCMDLautomatic
             Just p' -> return (p',cm')

     -- try to prepare the theory
     prep <- case prepareForConsChecking st p_cm of
             Result _ Nothing ->
               do
                p_cm'@(prv',acm'@(Comorphism cid)) <-
                          lookupKnownConsChecker st P.ProveCMDLautomatic
                putStrLn ("Analyzing node " ++ ndnm)
                putStrLn ("Using the comorphism " ++ language_name cid)
                putStrLn ("Using consistency checker " ++ getPName prv')
                return $ case prepareForConsChecking st p_cm' of
                          Result _ Nothing -> Nothing
                          Result _ (Just sm)-> Just (sm,acm')
             Result _ (Just sm) -> return $ Just (sm,acm)
     case prep of
     -- theory could not be computed
      Nothing -> do
                  return "No suitable prover and comorphism found"
      Just (G_theory_with_cons_checker lid1 th p, cmp)->
       do
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
                      (P.Tactic_script $ show sTxt)
                      th []
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


-- | Given a proofstatus the function does the actual call of the
-- prover for proving the node or check consistency
proveNode ::
              --use theorems is subsequent proofs
              Bool ->
              -- save problem file for each goal
              Bool ->
              -- Tactic script
              ATPTactic_script ->
              -- proofState of the node that needs proving
              -- all theorems, goals and axioms should have
              -- been selected before,but the theory should have
              -- not beed recomputed
              Int_NodeInfo ->
              -- node name
              String ->
              -- selected prover, if non one will be automatically
              -- selected
              Maybe G_prover ->
              -- selected comorphism, if non one will be automatically
              -- selected
              Maybe AnyComorphism ->
              MVar (Maybe ThreadId) ->
              MVar (Maybe Int_NodeInfo)  ->
              MVar LibEnv ->
              LIB_NAME ->
              -- returns an error message if anything happens
               IO String
proveNode useTh save2File sTxt ndpf ndnm mp mcm mThr mSt mlbE libname
 =do
   case ndpf of
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
                p_cm'@(prv',acm'@(Comorphism cid)) <-
                          lookupKnownProver st P.ProveCMDLautomatic
                putStrLn ("Analyzing node " ++ ndnm)
                putStrLn ("Using the comorphism " ++ language_name cid)
                putStrLn ("Using prover " ++ getPName prv')
                return $ case prepareForProving st p_cm' of
                          Result _ Nothing -> Nothing
                          Result _ (Just sm)-> Just (sm,acm')
             Result _ (Just sm) -> return $ Just (sm,acm)
     case prep of
     -- theory could not be computed
      Nothing -> do
                  return "No suitable prover and comorphism found"
      Just (G_theory_with_prover lid1 th p, cmp)->
       do
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
                      (P.Tactic_script $ show  sTxt)
                      th []
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
                  MVar  (Maybe Int_NodeInfo) ->
                  [P.Proof_status proof_tree] ->
                  IO ()
pollForResults lid acm mStop mData mState done
 =do
  let toPrint ls=map(\x->let txt = "Goal "++(P.goalName x)++" is "
                         in case P.goalStatus x of
                             P.Open _   ->txt++"still open."
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
              -> Int_NodeInfo
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
       let nwTh = G_theory lidT sigT indT (Map.union sensT gMap) startThId
           dGraph = lookupDGraph libname lbEnv
           oldContents = labDG dGraph node
           newContents = oldContents {dgn_theory = nwTh}
           nextDGraph = changeDGH dGraph
               $ SetNodeLab oldContents (node, newContents)
       return $ Map.insert libname nextDGraph lbEnv


-- | Signal handler that stops the prover from running
-- when SIGINT is send
sigIntHandler :: MVar (Maybe ThreadId) ->
                 MVar LibEnv ->
                 MVar (Maybe Int_NodeInfo) ->
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
             MVar (Maybe Int_NodeInfo)  ->
             MVar LibEnv ->
             IntIState ->
             [Int_NodeInfo] ->
             IO ()
proveLoop mlbE mThr mSt mOut pS ls
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
                                                  $ getAllNodes pS of
                                               Nothing -> "Unkown node"
                                               Just (_,ll) ->
                                                 getDGNodeName ll
           putStrLn ("Analyzing node " ++ nodeName x)
           err <- proveNode (useTheorems pS)
                            (save2file pS)
                            (script pS)
                            x
                            (nodeName x)
                            (prover pS)
                            (cComorphism pS)
                            mThr
                            mSt
                            mlbE
                            (i_ln pS)
           case err of
            [] -> proveLoop mlbE mThr mSt mOut pS l
            _  -> do
                  putStrLn err
                  proveLoop mlbE mThr mSt mOut pS l

consCheckLoop :: MVar LibEnv ->
                 MVar (Maybe ThreadId) ->
                 MVar (Maybe Int_NodeInfo) ->
                 MVar LibEnv ->
                 IntIState ->
                 [Int_NodeInfo] ->
                 IO ()
consCheckLoop mlbE mThr mSt mOut pS  ls
 = case ls of
    -- we are done
    [] -> do
           nwLbEnv <- readMVar mlbE
           putMVar mOut nwLbEnv
           return ()
    x:l ->
         do
          let nodeName x' = case x' of
                             Element _ t -> case find(\(n,_) -> n==t) $
                                                  getAllNodes pS of
                                              Nothing -> "Unknown node"
                                              Just (_,ll) ->
                                                 getDGNodeName ll
          putStrLn ("Analyzing node " ++ nodeName x)
          err <- checkNode (useTheorems pS)
                           (save2file pS)
                           (script pS)
                           x
                           (nodeName x)
                           (consChecker pS)
                           (cComorphism pS)
                           mThr
                           mSt
                           mlbE
                           (i_ln pS)
          case err of
           [] -> consCheckLoop mlbE mThr mSt mOut pS l
           _ -> do
                 putStrLn err
                 consCheckLoop mlbE mThr mSt mOut pS l
