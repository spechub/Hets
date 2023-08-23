{- |
Module      :  ./Proofs/BatchProcessing.hs
Description :  Batch processing functions.
Copyright   :  (c) Klaus Luettich, Rainer Grabbe 2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Prover)

Functions for batch processing. Used by SoftFOL provers.
-}

module Proofs.BatchProcessing
  ( batchTimeLimit
  , isTimeLimitExceeded
  , adjustOrSetConfig
  , filterOpenGoals
  , checkGoal
  , goalProcessed
  , genericProveBatch
  , genericCMDLautomaticBatch
  ) where

import Logic.Prover

import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Id as Id
import qualified Data.Map as Map
import Common.Result

import Data.List
import Data.Maybe

import qualified Control.Exception as Exception
import qualified Control.Concurrent as Conc
import Control.Monad (when)

import Interfaces.GenericATPState

-- * Non-interactive Batch Prover

-- ** Constants

{- |
  Time limit used by the batch mode prover.
-}
batchTimeLimit :: Int
batchTimeLimit = 20

-- ** Utility Functions

{- |
  Checks whether an ATPRetval indicates that the time limit was
  exceeded.
-}
isTimeLimitExceeded :: ATPRetval -> Bool
isTimeLimitExceeded ATPTLimitExceeded = True
isTimeLimitExceeded _ = False


{- |
  Adjusts the configuration associated to a goal by applying the supplied
  function or inserts a new emptyConfig with the function applied if there's
  no configuration associated yet.

  Uses Map.member, Map.adjust, and Map.insert for the corresponding tasks
  internally.
-}
adjustOrSetConfig :: (Ord proof_tree) =>
                     (GenericConfig proof_tree -> GenericConfig proof_tree)
                     {- ^ function to be applied against the current
                     configuration or a new emptyConfig -}
                  -> String -- ^ name of the prover
                  -> ATPIdentifier -- ^ name of the goal
                  -> proof_tree -- ^ initial empty proof_tree
                  -> GenericConfigsMap proof_tree -- ^ current GenericConfigsMap
                  -> GenericConfigsMap proof_tree
                  -- ^ resulting GenericConfigsMap with the changes applied
adjustOrSetConfig f prName k pt m =
  if Map.member k m then Map.adjust f k m else
      Map.insert k (f $ emptyConfig prName k pt) m

filterOpenGoals :: GenericConfigsMap proof_tree -> GenericConfigsMap proof_tree
filterOpenGoals = Map.filter $ isOpenGoal . goalStatus . proofStatus

{- |
  Checks whether a goal in the results map is marked as proved.
-}
checkGoal :: GenericConfigsMap proof_tree -> ATPIdentifier -> Bool
checkGoal cfgMap goal =
  maybe False (isProvedStat . proofStatus) $ Map.lookup goal cfgMap

-- ** Callbacks

{- |
  Called every time a goal has been processed in the batch mode.
-}

goalProcessed :: (Ord proof_tree) =>
                 Conc.MVar (GenericState sentence proof_tree pst)
                 -- ^ IORef pointing to the backing State data structure
              -> Int -- ^ batch time limit
              -> [String] -- ^ extra options
              -> Int -- class Unpair f where  Source^ total number of goals
              -> String -- ^ name of the prover
              -> Int -- ^ number of goals processed so far
              -> AS_Anno.Named sentence -- ^ goal that has just been processed
              -> Bool -- ^ wether to be verbose: print goal status (CMDL mode)
              -> (ATPRetval, GenericConfig proof_tree)
              -> IO Bool
goalProcessed stateMVar tLimit extOpts numGoals prName processedGoalsSoFar
              nGoal verbose (retval, res_cfg)
              = do
                goalPair <- goalProcRetVal stateMVar tLimit extOpts
                            numGoals prName processedGoalsSoFar nGoal verbose (retval, res_cfg)
                return $ fst goalPair

-- same function as goalProcessed but it also returnes the goalStatus
goalProcRetVal :: (Ord proof_tree) =>
                 Conc.MVar (GenericState sentence proof_tree pst)
                 -- ^ IORef pointing to the backing State data structure
              -> Int -- ^ batch time limit
              -> [String] -- ^ extra options
              -> Int -- class Unpair f where  Source^ total number of goals
              -> String -- ^ name of the prover
              -> Int -- ^ number of goals processed so far
              -> AS_Anno.Named sentence -- ^ goal that has just been processed
              -> Bool -- ^ wether to be verbose: print goal status (CMDL mode)
              -> (ATPRetval, GenericConfig proof_tree)
              -> IO (Bool, GoalStatus)
goalProcRetVal stateMVar tLimit extOpts numGoals prName processedGoalsSoFar
              nGoal verbose (retval, res_cfg) = do
  let n = proofStatus res_cfg
  Conc.modifyMVar_ stateMVar $ \ s -> return $ s
    { configsMap = adjustOrSetConfig (\ c -> c
        { timeLimitExceeded = isTimeLimitExceeded retval
        , timeLimit = Just tLimit
        , extraOpts = extOpts
        , proofStatus = n { usedTime = timeUsed res_cfg}
        , resultOutput = resultOutput res_cfg
        , timeUsed = timeUsed res_cfg
        }) prName (AS_Anno.senAttr nGoal) (currentProofTree s) (configsMap s)}
  let
    theGoalStatus = goalStatus n
  when verbose $ putStrLn $ "Goal " ++ goalName n ++ " is "
    ++ case theGoalStatus of
         Open _ -> "still open."
         Disproved -> "disproved."
         Proved _ -> "proved."
  return $ case retval of
    ATPError _ -> (False, theGoalStatus)
    ATPBatchStopped -> (False, theGoalStatus)
    _ -> (numGoals - processedGoalsSoFar > 0, theGoalStatus)

-- ** Implementation

{- |
  A non-GUI batch mode prover. The list of goals is processed sequentially.
  Proved goals are inserted as axioms.
-}
genericProveBatch :: (Show sentence, Ord sentence, Ord proof_tree) =>
                     Bool -- ^ True means use tLimit\/options from GenericState
                  -> Int -- ^ batch time limit
                  -> [String] -- ^ extra options passed
                  -> Bool -- ^ True means include proved theorems
                  -> Bool -- True means save problem file
                  -> (Int
                      -> AS_Anno.Named sentence
                      -> Maybe (AS_Anno.Named sentence)
                      -> (ATPRetval, GenericConfig proof_tree)
                      -> IO Bool)
                      {- ^ called after every prover run.
                      return True if you want the prover to continue. -}
                  -> (pst -> AS_Anno.Named sentence -> pst)
                      -- ^ inserts a Namend sentence into a logicalPart
                  -> RunProver sentence proof_tree pst -- prover to run batch
                  -> String -- ^ prover name
                  -> String -- ^ theory name
                  -> GenericState sentence proof_tree pst
                  -> Maybe (Conc.MVar (Result [ProofStatus proof_tree]))
                     -- ^ empty MVar to be filled after each proof attempt
                  -> IO [ProofStatus proof_tree]
                  -- ^ proof status for each goal
genericProveBatch useStOpt tLimit extraOptions inclProvedThs saveProblem_batch
                  afterEachProofAttempt
                  inSen runGivenProver prName thName st resultMVar =
    batchProve (proverState st) 0 [] (goalsList st)
  where
    openGoals = filterOpenGoals (configsMap st)
    addToLP g res pst =
        if isProvedStat res && inclProvedThs
        then inSen pst (g {AS_Anno.isAxiom = True, AS_Anno.wasTheorem = True})
        else pst
    batchProve _ _ resDone [] = return (reverse resDone)
    batchProve pst goalsProcessedSoFar resDone (g : gs) =
     let gName = AS_Anno.senAttr g
         pt = currentProofTree st
     in
      if Map.member gName openGoals
      then do
        -- putStrLn $ "Trying to prove goal: " ++ gName
        let initEmptyCfg = emptyConfig prName gName pt
            curCfg = Map.findWithDefault initEmptyCfg gName openGoals
            runConfig = initEmptyCfg
                { timeLimit = Just $
                              if useStOpt then fromMaybe tLimit $
                                                     timeLimit curCfg
                                          else tLimit
                , extraOpts = if useStOpt && (not . null $ extraOpts curCfg)
                                 then extraOpts curCfg
                                 else extraOptions }
        (err, res_cfg) <-
              runGivenProver pst runConfig saveProblem_batch thName g
        {- putStrLn $ prName ++ " returned: " ++ (show err)
        if the batch prover runs in a separate thread
        that's killed via killThread
        runGivenProver will return ATPBatchStopped. We have to stop the
        recursion in that case
        add proved goals as axioms -}
        let res0 = proofStatus res_cfg
            res = res0 { proofLines = resultOutput res_cfg,
              goalStatus = case goalStatus res0 of
                Open (Reason l) | err == ATPTLimitExceeded ->
                  Open (Reason $ "Timeout" : l)
                r -> r }
            pst' = addToLP g res pst
            goalsProcessedSoFar' = goalsProcessedSoFar + 1
            ioProofStatus = reverse (res : resDone)
        maybe (return ())
              (\ rr -> do
                 mOldVal <- Conc.tryTakeMVar rr
                 let newRes = appendDiags (atpRetvalToDiags gName err)
                              >> revertRenamingOfLabels st [res]
                     -- transform new result in Monad Result
                     newVal = maybe id (joinResultWith (++)) mOldVal newRes
                     -- concat the oldValue with the new Result
                 Conc.putMVar rr newVal)
              resultMVar
        cont <- afterEachProofAttempt goalsProcessedSoFar' g
                         (find ((`Map.member` openGoals) .
                                AS_Anno.senAttr) gs)
                         (err, res_cfg)
        if cont
           then batchProve pst' goalsProcessedSoFar' (res : resDone) gs
           else return ioProofStatus
      else batchProve (addToLP g (proofStatus $
                                  Map.findWithDefault
                                         (emptyConfig prName gName pt)
                                         gName $ configsMap st) pst)
                      goalsProcessedSoFar resDone gs

atpRetvalToDiags :: String -- ^ name of goal
                 -> ATPRetval -> [Diagnosis]
atpRetvalToDiags gName err = case err of
  ATPError msg ->
    [Diag { diagKind = Error, diagString = msg, diagPos = Id.nullRange }]
  ATPTLimitExceeded ->
    [Diag { diagKind = Warning
          , diagString = "Time limit exceeded (goal \"" ++ gName ++ "\")."
          , diagPos = Id.nullRange }]
  _ -> []

-- * Generic command line prover function

{- |
  Automatic command line prover using batch mode.
-}
genericCMDLautomaticBatch ::
        (Show sentence, Ord proof_tree, Ord sentence)
        => ATPFunctions sign sentence mor proof_tree pst {- ^ prover specific
                                                     functions -}
        -> Bool -- ^ True means include proved theorems
        -> Bool -- ^ True means save problem file
        -> Conc.MVar (Result [ProofStatus proof_tree])
           -- ^ used to store the result of each attempt in the batch run
        -> String -- ^ prover name
        -> String -- ^ theory name
        -> ATPTacticScript -- ^ default prover specific tactic script
        -> Theory sign sentence proof_tree
           -- ^ theory consisting of a signature and a list of Named sentence
        -> [FreeDefMorphism sentence mor] -- ^ freeness constraints
        -> proof_tree -- ^ initial empty proof_tree
        -> IO (Conc.ThreadId, Conc.MVar ())
           {- ^ fst: identifier of the batch thread for killing it
           snd: MVar to wait for the end of the thread -}
genericCMDLautomaticBatch atpFun inclProvedThs saveProblem_batch resultMVar
                          prName thName defaultTacticScript th freedefs pt = do
    -- putStrLn $ show defaultTacticScript
    let iGS = initialGenericState prName
                                  (initialProverState atpFun)
                                  (atpTransSenName atpFun) th freedefs pt
    stateMVar <- Conc.newMVar iGS
    let tLimit = tsTimeLimit defaultTacticScript
        extOpts = tsExtraOpts defaultTacticScript
        numGoals = Map.size $ filterOpenGoals $ configsMap iGS
    mvar <- Conc.newEmptyMVar
    threadID <- Conc.forkIO
                 (when (numGoals > 0)
                  (genericProveBatch True tLimit extOpts inclProvedThs
                                      saveProblem_batch
                        (\ gPSF nSen _ conf ->
                             goalProcessed stateMVar tLimit extOpts numGoals
                                           prName gPSF nSen True conf)
                        (atpInsertSentence atpFun) (runProver atpFun)
                        prName thName iGS (Just resultMVar)
                      >> return ())
                   `Exception.finally` Conc.putMVar mvar ())
    return (threadID, mvar)
