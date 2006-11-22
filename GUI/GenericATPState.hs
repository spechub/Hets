{- |
Module      :  $Header$
Description :  Help functions for GUI.GenericATP
Copyright   :  (c) Klaus L�ttich, Rainer Grabbe, Uni Bremen 2006
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
import qualified Common.OrderedMap as OMap
import Common.ProofUtils

import Data.List

import Text.Regex


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
    resultOutput :: [String],
    -- | global time used in milliseconds
    timeUsed :: Int
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
                   resultOutput = [],
                   timeUsed = 0
                  }

{- |
  Performs a lookup on the ConfigsMap. Returns the config for the goal or an
  empty config if none is set yet.
-}
getConfig :: (Ord proof_tree) =>
             String -- ^ name of the prover
          -> ATPIdentifier -- ^ name of the goal
          -> proof_tree -- ^ initial empty proof_tree
          -> GenericConfigsMap proof_tree
          -> GenericConfig proof_tree
getConfig prName genid pt m = maybe (emptyConfig prName genid pt)
                                id lookupId
  where
    lookupId = Map.lookup genid m

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
    -- | currently selected goal or Nothing
    currentGoal :: Maybe ATPIdentifier,
    -- | initial empty proof_tree
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
    proverState :: pst
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
                    -> proof_tree -- ^ initial empty proof_tree
                    -> GenericState sign sentence proof_tree pst
initialGenericState prName ips trSenName th pt =
    GenericState {currentGoal = Nothing,
                  proof_tree = pt,
                  configsMap = Map.fromList $
                               map (\ g ->
                                        let gName = AS_Anno.senName g
                                            ec = emptyConfig prName gName pt
                                        in (gName, ec {proof_status =
                       updateTactic_script (proof_status ec) gName}))
                                   goals,
                  namesMap = collectNameMapping nSens oSens',
                  goalsList = goals,
                  proverState = ips sign oSens'
                 }
    where Theory sign oSens = th
          -- Search in list of Proof_status for first occurence of an Open goal
          -- with non-empty Tactic_script and update Tactic_script if found.
          updateTactic_script prStat gn =
            maybe prStat
                  (\senSt ->
                    let validThmStatus = filter (\tStatus ->
                            (goalStatus tStatus == Open) &&
                            (not $ tacticScript tStatus == Tactic_script ""))
                                                $ thmStatus senSt
                    in  if null validThmStatus
                          then prStat
                          else prStat { tacticScript = tacticScript
                                                       $ head validThmStatus })
                  $ OMap.lookup gn oSens
          oSens' = toNamedList oSens
          nSens = prepareSenNames trSenName oSens'
          goals = filter (not . AS_Anno.isAxiom) nSens
          


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
  -- | ATP batch mode was stopped with killthread
  | ATPBatchStopped
  deriving (Eq, Show)

type RunProver sentence proof_tree pst =
        pst -- ^ prover state containing logical part
        -> GenericConfig proof_tree -- ^ configuration to use
        -> Bool -- ^ True means save problem file
        -> String -- ^ name of the theory in the DevGraph
        -> AS_Anno.Named sentence -- ^ goal to prove
        -> IO (ATPRetval, GenericConfig proof_tree) -- ^ (retval, configuration with proof_status and complete output)

{- |
  Prover specific functions
-}
data ATPFunctions sign sentence proof_tree pst = ATPFunctions {
    -- | initial prover specific state
    initialProverState :: InitialProverState sign sentence pst,
    -- | prover specific translation of goal name
    atpTransSenName :: TransSenName,
    -- | inserts a goal into prover state
    atpInsertSentence :: pst -> AS_Anno.Named sentence -> pst,
    -- | output of a goal in a prover specific format
    goalOutput :: pst -> AS_Anno.Named sentence-> [String] -> IO String,
    -- | help text
    proverHelpText :: String,
    -- | environment variable containing time limit for batch time
    batchTimeEnv :: String,
    -- | file extensions for all output formats
    fileExtensions :: FileExtensions,
    -- | runs the prover
    runProver :: RunProver sentence proof_tree pst,
    -- | list of all options the prover finally runs with
    createProverOptions :: GenericConfig proof_tree -> [String]
  }

{- |
  File extensions for all prover specific output formats.
  Given extensions should begin with a dot.
-}
data FileExtensions = FileExtensions {
    -- | file extension for saving problem
    problemOutput :: String,
    -- | file extension for saving prover output
    proverOutput :: String,
    -- | file extension for saving theory configuration
    theoryConfiguration :: String
  }

{- |
  Tactic script implementation for ATPs. Read and show functions are provided.
-}
data ATPTactic_script = ATPTactic_script
    { ts_timeLimit :: Int, -- ^ used time limit
      ts_extraOpts :: [String] -- ^ used extra options (if any)
    } deriving (Eq, Ord)


instance Show ATPTactic_script where
  show ts = "Time limit: " ++ (show $ ts_timeLimit ts)
            ++ "\nExtra options: " ++ (show $ ts_extraOpts ts)

instance Read ATPTactic_script where
  readsPrec _ ts =
      let emptyATPTactic_script = ATPTactic_script {
                                  ts_timeLimit = 0, ts_extraOpts = [] }
          re_atp = mkRegex "Time limit: +([0-9]+).*\nExtra options: +(.*) *"
          readMatch = matchRegex re_atp ts
      in  maybe [(emptyATPTactic_script, "")]
                (\sl -> [(ATPTactic_script {
                              ts_timeLimit = (read $ sl !! 0) :: Int,
                              ts_extraOpts = (read $ sl !! 1) :: [String]}
                  , "")])
                readMatch
