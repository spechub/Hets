{- |
Module      :$Header$
Description : CMDL interface commands
Copyright   : uni-bremen and DFKI
License     : GPLv2 or higher, see LICENSE.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

CMDL.ProveConsistency contains prove and consistency check command
-}


module CMDL.ProveConsistency
       ( cProver
       , cConsChecker
       , doLoop
       , sigIntHandler
       ) where

import Interfaces.Command
import Interfaces.DataTypes
import Interfaces.GenericATPState(ATPTacticScript(..))
import Interfaces.History
import Interfaces.Utils (updateNodeProof)

import CMDL.DataTypes(CmdlState(intState))
import CMDL.DataTypesUtils(getAllNodes, add2hist, genErrorMsg, genMessage)
import CMDL.Utils(checkPresenceProvers)

import Comorphisms.LogicGraph(logicGraph)

import Proofs.AbstractState

import Static.DevGraph
import Static.GTheory(G_theory(G_theory), coerceThSens, startThId, sublogicOfTh)
import Static.History

import Logic.Comorphism
import Logic.Grothendieck
import Logic.Logic
import qualified Logic.Prover as P

import Common.Consistency
import Common.LibName(LibName)
import Common.Result(Result(Result))
import Common.Utils(trim)

import Data.List
import qualified Data.Map as Map

import Control.Concurrent(ThreadId, killThread)
import Control.Concurrent.MVar(MVar, newMVar, putMVar, takeMVar, readMVar,
                               swapMVar, modifyMVar_)

import Control.Monad

getProversAutomatic :: G_sublogics -> [(G_prover, AnyComorphism)]
getProversAutomatic sl =
  getProvers P.ProveCMDLautomatic (Just sl) $ findComorphismPaths logicGraph sl

-- | Select a prover
cProver::String -> CmdlState -> IO CmdlState
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
      Element z _ :_ -> let sl = sublogicOfTheory z in
        -- see if any comorphism was used
       case cComorphism pS of
       -- if none use the theory  of the first selected node
       -- to find possible comorphisms
       Nothing-> case find (\ (y, _)-> getPName y == inp)
                 $ getProversAutomatic sl of
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
         case find (\ (y, _)-> getPName y == inp)
         $ getProvers P.ProveCMDLautomatic (Just sl) [x] of
            Nothing ->
             case find (\(y,_) -> getPName y == inp)
               $ getProversAutomatic sl of
               Nothing -> return $ genErrorMsg ("No applicable prover with"
                                          ++ " this name found") state
               Just (p,nCm@(Comorphism cid))->
                 return $ add2hist [(ProverChange $ prover pS),
                                    (CComorphismChange $ cComorphism pS)]
                     $ genMessage "" ("Hint: Using default comorphism `"
                            ++ language_name cid ++ "`")
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
                             getConsCheckers $ findComorphismPaths
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
                     $ getConsCheckers [x] of
           Nothing ->
            case find (\(y,_) -> getPName y == inp) $ getConsCheckers $
                          findComorphismPaths logicGraph $ sublogicOfTh $
                          theory z of
             Nothing -> return $ genErrorMsg ("No applicable consistency "++
                                 "checker with this name found") state
             Just (p,nCm@(Comorphism cid)) ->
               return $ add2hist [(ConsCheckerChange $ consChecker pS),
                                  (CComorphismChange $ cComorphism pS)]
                  $ genMessage "" ("Hint: Using default comorphism `"
                      ++ language_name cid ++ "`")
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
checkNode :: -- Tactic script
              ATPTacticScript ->
              -- proofState of the node that needs proving
              -- all theorems, goals and axioms should have
              -- been selected before, but the theory should have
              -- not been recomputed
              Int_NodeInfo ->
              -- node name
              String ->
              -- selected prover, if non one will be automatically
              -- selected
              Maybe G_cons_checker ->
              -- selected comorphism, if non one will be automatically
              -- selected
              Maybe AnyComorphism ->
              MVar (Maybe Int_NodeInfo)  ->
              MVar IntState ->
              LibName ->
              -- returns an error message if anything happens
              IO String
checkNode sTxt ndpf ndnm mp mcm mSt miSt ln =
  case ndpf of
    Element pf_st nd ->
     do
     -- recompute the theory (to make effective the selected axioms,
     -- goals) !? needed?
     let st = recalculateSublogicAndSelectedTheory pf_st
     -- compute a prover,comorphism pair to be used in preparing
     -- the theory
     p_cm@(_, acm)<- case mcm of
           Nothing -> lookupKnownConsChecker st
           Just cm' -> case mp of
             Nothing -> lookupKnownConsChecker st
             Just p' -> return (p', cm')

     -- try to prepare the theory
     prep <- case prepareForConsChecking st p_cm of
             Result _ Nothing ->
               do
                p_cm'@(prv',acm'@(Comorphism cid)) <-
                          lookupKnownConsChecker st
                putStrLn ("Analyzing node for consistency " ++ ndnm)
                putStrLn ("Using the comorphism " ++ language_name cid)
                putStrLn ("Using consistency checker " ++ getPName prv')
                return $ case prepareForConsChecking st p_cm' of
                          Result _ Nothing -> Nothing
                          Result _ (Just sm)-> Just (sm, acm')
             Result _ (Just sm) -> return $ Just (sm, acm)
     case prep of
     -- theory could not be computed
      Nothing -> return "No suitable prover and comorphism found"
      Just (G_theory_with_cons_checker _ th p, _)->
        case P.ccAutomatic p of
         fn ->
          do
          let st' = st { proverRunning = True}
          -- store initial input of the prover
          let tLimit = show $ tsTimeLimit sTxt
          swapMVar mSt $ Just $ Element st' nd
          cstat <- fn (theoryName st)
                      (P.TacticScript tLimit)
                      th []
          swapMVar mSt $ Just $ Element st nd
          putStrLn $ case P.ccResult cstat of
            Nothing -> "Timeout after " ++ tLimit ++ "seconds."
            Just b -> "node " ++ ndnm ++ " is "
              ++ (if b then "" else "in") ++ "consistent."
          ist <- readMVar miSt
          case i_state ist of
            Nothing -> return "no library"
            Just iist -> case P.ccResult cstat of
             Nothing -> return ""
             Just b -> do
              let le = i_libEnv iist
                  dg = lookupDGraph ln le
                  nl = labDG dg nd
                  nn = getDGNodeName nl
                  newDg0 = changeDGH dg $ SetNodeLab nl (nd,
                    markNodeConsistency
                    (if b then Cons else Inconsistent) "" nl)
                  newDg = groupHistory dg (DGRule "Consistency check") newDg0
                  nst = add2history
                    (CommentCmd $ "consistency check done on " ++ nn ++ "\n")
                    ist $ [DgCommandChange ln]
                  nwst = nst { i_state =
                           Just iist { i_libEnv = Map.insert ln newDg le } }
              swapMVar miSt nwst
              return ""

-- | Given a proofstatus the function does the actual call of the
-- prover for proving the node or check consistency
proveNode ::
              --use theorems is subsequent proofs
              Bool ->
              -- save problem file for each goal
              Bool ->
              -- Tactic script
              ATPTacticScript ->
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
              MVar IntState ->
              LibName ->
              -- returns an error message if anything happens
               IO String
proveNode useTh save2File sTxt ndpf ndnm mp mcm mThr mSt miSt libname =
  case ndpf of
    Element pf_st nd ->
     do
     -- recompute the theory (to make effective the selected axioms,
     -- goals)
     let st = recalculateSublogicAndSelectedTheory pf_st
     -- compute a prover,comorphism pair to be used in preparing
     -- the theory
     p_cm@(_,acm) <- case mcm of
           Nothing -> lookupKnownProver st P.ProveCMDLautomatic
           Just cm' -> case mp of
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
             tmp <- fn useTh
                      save2File
                      answ
                      (theoryName st)
                      (P.TacticScript $ show  sTxt)
                      th []
             swapMVar mThr $ Just $ fst tmp
             getResults lid1 cmp (snd tmp) answ mSt
             swapMVar mThr Nothing
             ist  <- readMVar miSt
             state <- readMVar mSt
             case state of
              Nothing -> return ""
              Just state' ->
               do
                swapMVar mSt Nothing
                swapMVar miSt $ addResults ist libname state'
                return ""

getResults :: (Logic lid sublogics basic_spec sentence
                     symb_items symb_map_items
                     sign morphism symbol raw_symbol proof_tree) =>
              lid ->
              AnyComorphism ->
              MVar () ->
              MVar (Result [P.ProofStatus proof_tree]) ->
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
addResults :: IntState -> LibName -> Int_NodeInfo -> IntState
addResults ist libname ndps =
  case i_state ist of
    Nothing -> ist
    Just pS ->
      case ndps of
       Element ps'' node -> case theory ps'' of
         G_theory lidT sigT indT sensT _ ->
           case coerceThSens (logicId ps'') lidT "" (goalMap ps'') of
             Nothing -> ist
             Just gMap -> let
               nwTh = G_theory lidT sigT indT (Map.union sensT gMap) startThId
               dGraph = lookupDGraph libname (i_libEnv pS)
               nl = labDG dGraph node
               in fst $ updateNodeProof libname ist (node, nl) (Just nwTh)

-- | Signal handler that stops the prover from running
-- when SIGINT is send
sigIntHandler :: MVar (Maybe ThreadId) ->
                 MVar IntState ->
                 MVar (Maybe Int_NodeInfo) ->
                 ThreadId ->
                 MVar IntState ->
                 LibName ->
                 IO ()
sigIntHandler mthr miSt mSt thr mOut libname =
  do
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
   ist <- readMVar miSt
   st <- readMVar mSt
   -- add to the output mvar results until now
   putMVar mOut $ case st of
     Nothing -> ist
     Just st' -> addResults ist libname st'
   return ()

doLoop :: MVar IntState
       -> MVar (Maybe ThreadId)
       -> MVar (Maybe Int_NodeInfo)
       -> MVar IntState
       -> [Int_NodeInfo]
       -> Bool
       -> IO ()
doLoop miSt mThr mSt mOut ls checkCons = do
  ist <- readMVar miSt
  case i_state ist of
    Nothing -> do
                 putMVar mOut ist
                 return ()
    Just pS ->
        case ls of
         -- we are done
          [] -> do
                 putMVar mOut ist
                 return ()
          x : l -> do
                 let nodeName x' = case x' of
                       Element _ t -> case lookup t $ getAllNodes pS of
                         Nothing -> "Unkown node"
                         Just ll -> getDGNodeName ll
                 putStrLn ("Analyzing node " ++ nodeName x)
                 err <- if checkCons
                           then checkNode (script pS)
                                          x
                                          (nodeName x)
                                          (consChecker pS)
                                          (cComorphism pS)
                                          mSt
                                          miSt
                                          (i_ln pS)
                           else proveNode (useTheorems pS)
                                          (save2file pS)
                                          (script pS)
                                          x
                                          (nodeName x)
                                          (prover pS)
                                          (cComorphism pS)
                                          mThr
                                          mSt
                                          miSt
                                          (i_ln pS)
                 unless (null err) (putStrLn err)
                 doLoop miSt mThr mSt mOut l checkCons
