{- |
Module      :$Header$
Description : CMDL interface commands
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

CMDL.ProveConsistency contains prove and consistency check command
-}


module CMDL.ProveConsistency
       ( cProver
       , cConsChecker
       , checkNode
       , proveNode
       , proveLoop
       , consCheckLoop
       , sigIntHandler
       ) where


import Interfaces.DataTypes
import Interfaces.GenericATPState(ATPTactic_script)

import CMDL.DataTypes(CmdlState(intState))
import CMDL.DataTypesUtils(getAllNodes, add2hist, genErrorMsg, genMessage)
import CMDL.Utils(checkPresenceProvers)

import Comorphisms.LogicGraph(logicGraph)

import Proofs.EdgeUtils(changeDGH)
import Proofs.AbstractState

import Static.DevGraph(LibEnv, DGNodeLab(dgn_theory), DGChange(SetNodeLab),
                       getDGNodeName, labDG, lookupDGraph)
import Static.GTheory(G_theory(G_theory), coerceThSens, startThId, sublogicOfTh)

import Logic.Comorphism(AnyComorphism(..), Comorphism(targetLogic))
import Logic.Grothendieck(findComorphismPaths)
import Logic.Logic(Language(language_name), Logic(provers))
import qualified Logic.Prover as P

import Common.LibName(LIB_NAME)
import Common.Result(Result(Result))
import Common.Utils(trim)

import Data.List
import qualified Data.Map as Map

import Control.Concurrent(ThreadId, killThread)
import Control.Concurrent.MVar(MVar, newMVar, putMVar, takeMVar, readMVar,
                               swapMVar, modifyMVar_)

import System.IO(IO, putStrLn)



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
cProver::String -> CmdlState ->
                    IO CmdlState
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
       Nothing-> case find (\(y,_)-> getPName y == inp) $
                      getProversAutomatic $ findComorphismPaths logicGraph $
                      sublogicOfTh $ theory z of
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
         case find (\(y,_)-> getPName y == inp) $ getProversAutomatic [x] of
            Nothing ->
             case find (\(y,_) -> getPName y == inp) $ getProversAutomatic $
                  findComorphismPaths logicGraph $ sublogicOfTh $ theory z of
               Nothing -> return $ genErrorMsg ("No applicable prover with"
                                          ++ " this name found") state
               Just (p,nCm@(Comorphism cid))->
                 return $ add2hist [(ProverChange $ prover pS),
                                    (CComorphismChange $ cComorphism pS)]
                     $ genMessage [] ("Warning: Prover can't be used with "
                            ++ "the selected comorphism (or the default if "
                            ++ "none was selected). Instead the `"
                            ++ language_name cid
                            ++ "` comorphism was selected. Current prover is "
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
cConsChecker::String -> CmdlState -> IO CmdlState
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
          case find(\(y,_) -> getPName y == inp)
                     $ getConsCheckersAutomatic [x] of
           Nothing ->
            case find (\(y,_) -> getPName y == inp)$ getConsCheckersAutomatic $
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
 = case ndpf of
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
      Nothing -> return "No suitable prover and comorphism found"
      Just (G_theory_with_cons_checker lid1 th p, cmp)->
        case P.proveCMDLautomaticBatch p of
         Nothing -> return "Error obtaining the prover"
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
             getResults lid1 cmp (snd tmp) answ mSt
             swapMVar mThr Nothing
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
 = case ndpf of
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
      Nothing -> return "No suitable prover and comorphism found"
      Just (G_theory_with_prover lid1 th p, cmp)->
        case P.proveCMDLautomaticBatch p of
         Nothing -> return "Error obtaining the prover"
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
             getResults lid1 cmp (snd tmp) answ mSt
             swapMVar mThr Nothing
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

getResults :: (Logic lid sublogics basic_spec sentence
                     symb_items symb_map_items
                     sign morphism symbol raw_symbol proof_tree) =>
              lid ->
              AnyComorphism ->
              MVar () ->
              MVar (Result [P.Proof_status proof_tree]) ->
              MVar (Maybe Int_NodeInfo) ->
              IO ()
getResults lid acm mStop mData mState =
  do
    takeMVar mStop
    d <- takeMVar mData
    case d of
      Result _ Nothing   -> return ()
      Result _ (Just d') -> modifyMVar_ mState
        (\ s -> case s of
                  Nothing -> return s
                  Just (Element st node) -> return $ Just $ Element
                                            (markProved acm lid d' st) node)

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
