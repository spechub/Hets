{- |
Module      : ./CMDL/ProveConsistency.hs
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
import Interfaces.GenericATPState (ATPTacticScript (..))
import Interfaces.History
import Interfaces.Utils

import CMDL.DataTypes (CmdlState (intState), ProveCmdType (..))
import CMDL.DataTypesUtils

import Comorphisms.LogicGraph (logicGraph)

import Proofs.AbstractState

import Static.DevGraph
import Static.DgUtils
import Static.History

import Common.DocUtils

import Logic.Comorphism
import Logic.Grothendieck
import Logic.Logic
import Logic.Prover as P
import Logic.Coerce

import Common.Consistency
import Common.LibName (LibName)
import Common.Result (Result (Result))
import Common.Utils (trim)

import qualified Common.OrderedMap as OMap
import Common.AS_Annotation

import Data.List
import qualified Data.HashMap.Lazy as Map

import Control.Concurrent (ThreadId, killThread)
import Control.Concurrent.MVar (MVar, newMVar, putMVar, takeMVar, readMVar,
                               swapMVar, modifyMVar_)

import Control.Monad

import Data.Foldable (forM_)

negate_th_with_cons_checker :: G_theory_with_cons_checker -> String ->
                               Maybe G_theory_with_cons_checker
negate_th_with_cons_checker g_th goal = case g_th of
  G_theory_with_cons_checker lid1 th cons_check ->
    case P.tTarget th of
      P.Theory lid2 sens -> case OMap.lookup goal sens of
        Nothing -> Nothing
        Just sen -> case negation lid1 $ sentence sen of
                                Nothing -> Nothing
                                Just sen' -> let
                                  negSen = sen { sentence = sen',
                                                 isAxiom = True }
                                  sens' = OMap.insert goal negSen $
                                           OMap.filter isAxiom sens
                                  target' = P.Theory lid2 sens'
                                 in Just $ G_theory_with_cons_checker lid1 th
                                            {P.tTarget = target'} cons_check

getProversAutomatic :: G_sublogics -> IO [(G_prover, AnyComorphism)]
getProversAutomatic sl = getUsableProvers P.ProveCMDLautomatic sl logicGraph

-- | Select a prover
cProver :: String -> CmdlState -> IO CmdlState
cProver input state =
  do
   -- trimed input
   let inp = trim input
   case i_state $ intState state of
    Nothing -> return $ genMsgAndCode "Nothing selected" 1 state
    Just pS ->
     -- check that some theories are selected
     case elements pS of
      [] -> return $ genMsgAndCode "Nothing selected" 1 state
      Element z _ : _ -> do
        prov <- getProversAutomatic (sublogicOfTheory z)
        let pl = filter ((== inp) . getProverName . fst) prov
            prover_names = map (getProverName . fst) prov
        case case cComorphism pS of
                   Nothing -> pl
                   Just x -> filter ((== x) . snd) pl ++ pl of
             [] -> if inp == "" then do
                            mapM_ putStrLn (nub prover_names)
                            return state
                               else return (genMsgAndCode
                 ("No applicable prover with name \"" ++ inp ++ "\" found") 1
                 state)
             (p, nCm@(Comorphism cid)) : _ ->
               return $ add2hist [ ProverChange $ prover pS
                                 , CComorphismChange $ cComorphism pS ]
                     $ genMessage "" ("Hint: Using comorphism `"
                            ++ language_name cid ++ "`")
                            state {
                              intState = (intState state) {
                                i_state = Just pS
                                             { cComorphism = Just nCm
                                             , prover = Just p } } }

-- | Selects a consistency checker
cConsChecker :: String -> CmdlState -> IO CmdlState
cConsChecker input state =
  do
   -- trimed input
   let inp = trim input
   case i_state $ intState state of
    Nothing -> return $ genMsgAndCode "Nothing selected" 1 state
    Just pS ->
     -- check that some theories are selected
     case elements pS of
      [] -> return $ genMsgAndCode "Nothing selected" 1 state
      Element z _ : _ ->
       do
        consCheckList <- getConsCheckers $ findComorphismPaths
                                logicGraph $ sublogicOfTheory z
        -- see if any comorphism was used
        case cComorphism pS of
        {- if none use the theory of the first selected node
        to find possible comorphisms -}
         Nothing -> case find (\ (y, _) -> getCcName y == inp) consCheckList of
                    Nothing -> if inp == "" then do
                                            let shortConsCList = nub $ map
                                                 (\ (y, _) -> getCcName y)
                                                 consCheckList
                                            mapM_ putStrLn shortConsCList
                                            return state
                                          else return $ genMsgAndCode
                                ("No applicable " ++
                                 "consistency checker with this name found") 1
                                 state
                    Just (p, _) -> return $ add2hist
                                    [ConsCheckerChange $ consChecker pS]
                                    state {
                                      intState = (intState state) {
                                         i_state = Just pS {
                                             consChecker = Just p }
                                          }
                                      }
         Just x -> do
          cs <- getConsCheckers [x]
          case find (\ (y, _) -> getCcName y == inp) cs of
           Nothing ->
            case find (\ (y, _) -> getCcName y == inp) consCheckList of
             Nothing -> if inp == "" then do
                                            let shortConsCList = nub $ map
                                                 (\ (y, _) -> getCcName y)
                                                 consCheckList
                                            mapM_ putStrLn shortConsCList
                                            return state
                                    else return $ genMsgAndCode
                                ("No applicable " ++
                                 "consistency checker with this name found") 1
                                 state
             Just (p, nCm@(Comorphism cid)) ->
               return $ add2hist [ ConsCheckerChange $ consChecker pS
                                 , CComorphismChange $ cComorphism pS ]
                  $ genMessage "" ("Hint: Using default comorphism `"
                      ++ language_name cid ++ "`")
                      state {
                       intState = (intState state) {
                         i_state = Just pS {
                                    cComorphism = Just nCm,
                                    consChecker = Just p } } }
           Just (p, _) -> return
                           $ add2hist [ConsCheckerChange $ consChecker pS]
                            $ state {
                            intState = (intState state) {
                              i_state = Just pS { consChecker = Just p } } }

{- | Given a proofstatus the function does the actual call of the
prover for consistency checking -}

checkNode ::
              -- Tactic script
              ATPTacticScript ->
              {- proofState of the node that needs proving
              all theorems, goals and axioms should have
              been selected before, but the theory should have
              not been recomputed -}
              Int_NodeInfo ->
              -- node name
              String ->
              {- selected prover, if non one will be automatically
              selected -}
              Maybe G_cons_checker ->
              {- selected comorphism, if non one will be automatically
              selected -}
              Maybe AnyComorphism ->
              MVar (Maybe Int_NodeInfo) ->
              MVar IntState ->
              LibName ->
              -- returns an error message if anything happens
              IO String
checkNode sTxt ndpf ndnm mp mcm mSt miSt ln =
  case ndpf of
    Element pf_st nd ->
     do
     {- recompute the theory (to make effective the selected axioms,
     goals) !? needed? -}
     let st = recalculateSublogicAndSelectedTheory pf_st
     {- compute a prover,comorphism pair to be used in preparing
     the theory -}
     p_cm@(_, acm) <- case mcm of
           Nothing -> lookupKnownConsChecker st
           Just cm' -> case mp of
             Nothing -> lookupKnownConsChecker st
             Just p' -> return (p', cm')

     -- try to prepare the theory
     prep <- case prepareForConsChecking st p_cm of
             Result _ Nothing ->
               do
                p_cm'@(prv', acm'@(Comorphism cid)) <-
                          lookupKnownConsChecker st
                putStrLn ("Analyzing node for consistency " ++ ndnm)
                putStrLn ("Using the comorphism " ++ language_name cid)
                putStrLn ("Using consistency checker " ++ getCcName prv')
                return $ case prepareForConsChecking st p_cm' of
                          Result _ Nothing -> Nothing
                          Result _ (Just sm) -> Just (sm, acm')
             Result _ (Just sm) -> return $ Just (sm, acm)
     case prep of
     -- theory could not be computed
      Nothing -> return "No suitable prover and comorphism found"
      Just (G_theory_with_cons_checker _ th p, _) ->
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
              if showOutput iist then
                do
                  putStrLn "____________________________"
                  print $ P.ccProofTree cstat
                  putStrLn "____________________________"
                                   else putStr ""
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
                    ist [DgCommandChange ln]
                  nwst = nst { i_state =
                           Just iist { i_libEnv = Map.insert ln newDg le } }
              swapMVar miSt nwst
              return ""

{- | Given a proofstatus the function does the actual call of the
prover for proving the node or check consistency -}
proveNode ::
              -- use theorems is subsequent proofs
              Bool ->
              -- save problem file for each goal
              Bool ->
              -- Tactic script
              ATPTacticScript ->
              {- proofState of the node that needs proving
              all theorems, goals and axioms should have
              been selected before,but the theory should have
              not beed recomputed -}
              Int_NodeInfo ->
              -- node name
              String ->
              {- selected prover, if non one will be automatically
              selected -}
              Maybe G_prover ->
              {- selected comorphism, if non one will be automatically
              selected -}
              Maybe AnyComorphism ->
              MVar (Maybe ThreadId) ->
              MVar (Maybe Int_NodeInfo) ->
              MVar IntState ->
              LibName ->
              -- returns an error message if anything happens
              IO String
proveNode useTh save2File sTxt ndpf ndnm mp mcm mThr mSt miSt libname =
  case ndpf of
    Element pf_st nd ->
     do
     {- recompute the theory (to make effective the selected axioms,
     goals) -}
     let st = recalculateSublogicAndSelectedTheory pf_st
     {- compute a prover,comorphism pair to be used in preparing
     the theory -}
     p_cm@(_, acm) <- case mcm of
           Nothing -> lookupKnownProver st P.ProveCMDLautomatic
           Just cm' -> case mp of
             Nothing -> lookupKnownProver st P.ProveCMDLautomatic
             Just p' -> return (p', cm')

     -- try to prepare the theory
     prep <- case prepareForProving st p_cm of
             Result _ Nothing ->
               do
                p_cm'@(prv', acm'@(Comorphism cid)) <-
                          lookupKnownProver st P.ProveCMDLautomatic
                putStrLn ("Analyzing node " ++ ndnm)
                putStrLn ("Using the comorphism " ++ language_name cid)
                putStrLn ("Using prover " ++ getProverName prv')
                return $ case prepareForProving st p_cm' of
                          Result _ Nothing -> Nothing
                          Result _ (Just sm) -> Just (sm, acm')
             Result _ (Just sm) -> return $ Just (sm, acm)
     case prep of
     -- theory could not be computed
      Nothing -> return "No suitable prover and comorphism found"
      Just (G_theory_with_prover lid1 th p, cmp) -> 
        case P.proveCMDLautomaticBatch p of
         Nothing -> return "Error obtaining the prover"
         Just fn ->
          do
          -- mVar to poll the prover for results
          answ <- newMVar (return [])
          let st' = st { proverRunning = True}
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
             putStrLn "selectedGoals:"
             putStrLn $ unlines (selectedGoals st')
             tmp <- fn useTh
                      save2File
                      answ
                      (theoryName st)
                      (P.TacticScript $ show sTxt)
                      th []
             swapMVar mThr $ Just $ fst tmp
             getResults lid1 cmp (snd tmp) answ mSt th
             swapMVar mThr Nothing
             ist <- readMVar miSt
             state <- readMVar mSt
             case state of
              Nothing -> return ""
              Just state' ->
               do
                swapMVar mSt Nothing
                swapMVar miSt $ addResults ist libname state'
                return ""

disproveNode ::
               -- Tactic script
              ATPTacticScript ->
              {- proofState of the node that needs proving
              all theorems, goals and axioms should have
              been selected before, but the theory should have
              not been recomputed -}
              Int_NodeInfo ->
              -- node name
              String ->
              {- selected prover, if non one will be automatically
              selected -}
              Maybe G_cons_checker ->
              {- selected comorphism, if non one will be automatically
              selected -}
              Maybe AnyComorphism ->
              MVar (Maybe Int_NodeInfo) ->
              MVar IntState ->
              LibName ->
              -- returns an error message if anything happens
              IO String
disproveNode sTxt ndpf ndnm mp mcm mSt miSt ln =
  case ndpf of
    Element pf_st nd ->
     do
     {- recompute the theory (to make effective the selected axioms,
     goals) !? needed? -}
     let st = recalculateSublogicAndSelectedTheory pf_st
     {- compute a prover,comorphism pair to be used in preparing
     the theory -}
     p_cm@(_, acm) <- case mcm of
           Nothing -> lookupKnownConsChecker st
           Just cm' -> case mp of
             Nothing -> lookupKnownConsChecker st
             Just p' -> return (p', cm')

     -- try to prepare the theory
     prep <- case prepareForConsChecking st p_cm of
             Result _ Nothing ->
               do
                p_cm'@(prv', acm'@(Comorphism cid)) <-
                          lookupKnownConsChecker st
                putStrLn ("Analyzing node for consistency " ++ ndnm)
                putStrLn ("Using the comorphism " ++ language_name cid)
                putStrLn ("Using consistency checker " ++ getCcName prv')
                return $ case prepareForConsChecking st p_cm' of
                          Result _ Nothing -> Nothing
                          Result _ (Just sm) -> Just (sm, acm')
             Result _ (Just sm) -> return $ Just (sm, acm)
     case prep of
     -- theory could not be computed
      Nothing -> return "No suitable prover and comorphism found"
      Just (theory@(G_theory_with_cons_checker l _ p), _) ->
        case P.ccAutomatic p of
         fn ->
          do
          let goals = selectedGoals st
              st' = st { proverRunning = True }
              negate_theory = negate_th_with_cons_checker theory
              theories = map negate_theory goals
              th_and_goals = zip theories goals
              disprove_goal (theory', goal) =
                case theory' of
                  Nothing -> return $ "Negating goal " ++ goal ++ " failed"
                  Just (G_theory_with_cons_checker l2 th' _) ->
                    do
                    -- store initial input of the prover
                    let tLimit = show $ tsTimeLimit sTxt
                    th2 <- coerceTheoryMorphism l2 l
                            "coerce error CMDL.ProveConsistency " th'
                    swapMVar mSt $ Just $ Element st' nd
                    cstat <- fn (theoryName st)
                          (P.TacticScript tLimit)
                          th2 []
                    swapMVar mSt $ Just $ Element st nd
                    putStrLn $ case P.ccResult cstat of
                      Nothing -> "Timeout after " ++ tLimit ++ "seconds."
                      Just b -> "goal " ++ goal ++ " is "
                        ++ (if b then "" else "not ") ++ "disproved."
                    ist <- readMVar miSt
                    case i_state ist of
                      Nothing -> return $ "goal " ++ goal ++ ": no library"
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
                            newDg = groupHistory dg
                                     (DGRule "Consistency check") newDg0
                            nst = add2history
                              (CommentCmd $ "disprove at goal " ++ goal ++
                                            ", node " ++ nn ++ "\n")
                              ist [DgCommandChange ln]
                            nwst = nst { i_state =
                                     Just iist { i_libEnv = Map.insert ln
                                                             newDg le } }
                        swapMVar miSt nwst
                        return ""
          mapM_ ((\ x -> do
                           y <- x
                           putStrLn y
                           return () ) . disprove_goal) th_and_goals
          return ""

getResults :: (Logic lid sublogics basic_spec sentence
                     symb_items symb_map_items
                     sign morphism symbol raw_symbol proof_tree, Pretty sentence) =>
              lid ->
              AnyComorphism ->
              MVar () ->
              MVar (Result [P.ProofStatus proof_tree]) ->
              MVar (Maybe Int_NodeInfo) -> 
              P.Theory sign sentence proof_tree ->
              IO ()
getResults lid acm mStop mData mState (P.Theory _ sensMap) =
  do
    takeMVar mStop
    d <- takeMVar mData
    case d of
      Result _ Nothing -> return ()
      Result _ (Just d') -> do
        mapM_ (\ gs -> let
                  uAx = map 
                          (\x -> let ax =  case OMap.lookup x sensMap of
                                            Nothing -> error "Proof using a missing axiom"
                                            Just s -> show $ pretty $ sentence s
                                  in x ++" : " ++ ax ++ "\n") $
                        P.usedAxioms gs
                in  
               putStrLn $ "Goal " ++ P.goalName gs
               ++ " used \n" ++ unwords uAx)
          $ filter P.isProvedStat d'
        modifyMVar_ mState (\ s -> case s of
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
       Element ps'' node -> let
               dGraph = lookupDGraph libname (i_libEnv pS)
               nl = labDG dGraph node
               in fst $ updateNodeProof libname ist (node, nl)
                      $ currentTheory ps''

{- | Signal handler that stops the prover from running
when SIGINT is send -}
sigIntHandler :: MVar (Maybe ThreadId) ->
                 MVar IntState ->
                 MVar (Maybe Int_NodeInfo) ->
                 ThreadId ->
                 MVar IntState ->
                 LibName ->
                 IO ()
sigIntHandler mthr miSt mSt thr mOut libname =
  do
   {- print a message
   ? shellputStr ! should be used ! -}
   putStrLn "Prover stopped."
   -- check if the prover is runnig
   tmp <- readMVar mthr
   Data.Foldable.forM_ tmp killThread
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
       -> ProveCmdType
       -> IO ()
doLoop miSt mThr mSt mOut ls proveCmdType = do
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
                 err <- case proveCmdType of
                           ConsCheck -> checkNode (script pS)
                                          x
                                          (nodeName x)
                                          (consChecker pS)
                                          (cComorphism pS)
                                          mSt
                                          miSt
                                          (i_ln pS)
                           Prove -> proveNode (useTheorems pS)
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
                           Disprove -> disproveNode (script pS)
                                             x
                                             (nodeName x)
                                             (consChecker pS)
                                             (cComorphism pS)
                                             mSt
                                             miSt
                                             (i_ln pS)
                 unless (null err) (putStrLn err)
                 doLoop miSt mThr mSt mOut l proveCmdType
