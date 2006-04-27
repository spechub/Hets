{- |
Module      :  $Header$
Description :  Help functions for GUI.GenericATP
Copyright   :  (c) Klaus Lüttich, Rainer Grabbe, Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rainer25@tzi.de
Stability   :  provisional
Portability :  ?

Data structures and initialising functions for Prover state and configurations.
Used by GUI.GenericATP.

-}

module GUI.GenericATPState where

import Logic.Prover

import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Lib.Map as Map
import Common.ProofUtils

import Data.List


-- * Data Structures

type ATPIdentifier = String

data GenericConfig proof_tree = GenericConfig {
    -- | Time limit in seconds passed
    -- to prover via extra option. Default will be used if Nothing.
    timeLimit :: Maybe Int,
    -- | True if timelimit exceeded during last prover run.
    timeLimitExceeded :: Bool,
    -- | Extra options passed verbatimely to prover.
    -- -DocProof, -Stdin, and -TimeLimit will be overridden.
    extraOpts :: [String],
    -- | Represents the result of a prover run.
    proof_status :: Proof_status proof_tree,
    resultOutput :: [String]
                               } deriving (Eq, Ord, Show)

{- |
  Creates an empty GenericConfig with a given goal name.
  Default time limit, no resultOutput and no extra options.
-}
emptyConfig :: (Ord proof_tree) =>
               String -- ^ name of the prover
            -> String -- ^ name of the goal
            -> proof_tree -- ^ initial empty proof_tree
            -> GenericConfig proof_tree
emptyConfig prName n pt =
    GenericConfig {timeLimit = Nothing,
                   timeLimitExceeded = False,
                   extraOpts = [],
                   proof_status = openProof_status n prName pt,
                   resultOutput = []
                  }

{- |
  We need to store one GenericConfig per goal.
-}
type GenericConfigsMap proof_tree = Map.Map ATPIdentifier
                                            (GenericConfig proof_tree)

{- |
  Map to identifiers
-}
type GenericGoalNameMap = Map.Map String String

{- |
  Represents the global state of the prover GUI.
-}
data GenericState sign sentence proof_tree pst = GenericState {
    currentGoal :: Maybe ATPIdentifier,
    proof_tree :: proof_tree,
    -- | stores the prover configurations for each goal
    -- and the results retrieved by running prover for each goal
    configsMap :: GenericConfigsMap proof_tree,
    -- | stores a mapping to SPASS compliant
    -- identifiers for all goals
    namesMap :: GenericGoalNameMap,
    -- | list of all goals
    goalsList :: [AS_Anno.Named sentence],
    -- | logical part without theorems
    proverState :: pst,
    batchModeIsRunning :: Bool,
    mainDestroyed :: Bool
  }

{- |
  Initialising the specific prover state containing logical part.
-}
type InitialProverState sign sentence pst =
        sign -> [AS_Anno.Named sentence] -> pst
type TransSenName = String -> String

{- |
  Creates an initial GenericState around a Theory.
-}
initialGenericState :: (Show sentence, Ord sentence, Ord proof_tree) =>
                       String -- ^ name of the prover
                    -> InitialProverState sign sentence pst
                    -> TransSenName
                    -> Theory sign sentence proof_tree
                    -> proof_tree
                    -> GenericState sign sentence proof_tree pst
initialGenericState prName ips trSenName th pt =
    GenericState {currentGoal = Nothing,
                  proof_tree = pt,
                  configsMap = Map.fromList $
                               map (\ g ->
                                        let gName = AS_Anno.senName g
                                        in (gName,
                                            emptyConfig prName gName pt))
                                   goals,
                  namesMap = collectNameMapping nSens oSens',
                  goalsList = goals,
                  proverState = ips sign oSens',
                  batchModeIsRunning = False,
                  mainDestroyed = False
                 }
    where Theory sign oSens = th
          oSens' = toNamedList oSens
          nSens = prepareSenNames trSenName oSens'
          (_, goals) = partition AS_Anno.isAxiom nSens

{- |
  Represents the general return value of a prover run.
-}
data ATPRetval
  -- | prover completed successfully
  = ATPSuccess
  -- | prover did not terminate before the time limit exceeded
  | ATPTLimitExceeded
  -- | an error occured while running the prover
  | ATPError String
  deriving (Eq, Show)

type RunProver sentence proof_tree pst =
        pst -- ^ prover state containing logical part
        -> GenericConfig proof_tree -- ^ configuration to use
        -> String -- ^ name of the theory in the DevGraph
        -> AS_Anno.Named sentence -- ^ goal to prove
        -> IO (ATPRetval, GenericConfig proof_tree) -- ^ (retval, configuration with proof_status and complete output)

{- |
  Prover specific functions
-}
data ATPFunctions sign sentence proof_tree pst = ATPFunctions {
    initialProverState :: InitialProverState sign sentence pst,
    atpTransSenName :: TransSenName,
    atpInsertSentence :: pst -> AS_Anno.Named sentence -> pst,
    dfgOutput :: pst -> AS_Anno.Named sentence-> IO String,
    proverHelpText :: String,
    batchTimeEnv :: String, -- ^ environment variable containing time limit for batch time
    fileExtensions :: (String, String), -- ^ file extensions for both prover output and configuration
    runProver :: RunProver sentence proof_tree pst
  }
