{- |
Module      :  $Header$
Description :  Help functions for GUI.GenericATP
Copyright   :  (c) Klaus Luettich, Rainer Grabbe, Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (regex-base needs MPTC+FD)

Data structures and initialising functions for Prover state and configurations.
Used by GUI.GenericATP.

-}

module Interfaces.GenericATPState where

import Logic.Prover

import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified Common.OrderedMap as OMap
import qualified Common.AS_Annotation as AS_Anno
import Common.ProofTree
import Common.ProofUtils
import Common.Result
import Common.Id
import Common.Doc
import Common.Utils

import Data.Maybe (fromMaybe)
import Data.Time (TimeOfDay, midnight)

import Control.Monad
import qualified Control.Exception as Exception

-- * Data Structures

type ATPIdentifier = String

data GenericConfig proof_tree = GenericConfig {
    {- | Time limit in seconds passed
    to prover via extra option. Default will be used if Nothing. -}
    timeLimit :: Maybe Int,
    -- | True if timelimit exceeded during last prover run.
    timeLimitExceeded :: Bool,
    {- | Extra options passed verbatimely to prover.
    -DocProof, -Stdin, and -TimeLimit will be overridden. -}
    extraOpts :: [String],
    -- | Represents the result of a prover run.
    proofStatus :: ProofStatus proof_tree,
    resultOutput :: [String],
    -- | global time used in milliseconds
    timeUsed :: TimeOfDay
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
                   proofStatus = openProofStatus n prName pt,
                   resultOutput = [],
                   timeUsed = midnight
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
getConfig prName genid pt m = fromMaybe (emptyConfig prName genid pt) lookupId
  where
    lookupId = Map.lookup genid m

{- |
  We need to store one GenericConfig per goal.
-}
type GenericConfigsMap proof_tree = Map.Map ATPIdentifier
                                            (GenericConfig proof_tree)

{- |
  New goal name mapped to old goal name
-}
type GenericGoalNameMap = Map.Map String String

{- |
  Represents the global state of the prover GUI.
-}
data GenericState sign sentence proof_tree pst = GenericState {
    -- | currently selected goal or Nothing
    currentGoal :: Maybe ATPIdentifier,
    -- | initial empty proof_tree
    currentProofTree :: proof_tree,
    {- | stores the prover configurations for each goal
    and the results retrieved by running prover for each goal -}
    configsMap :: GenericConfigsMap proof_tree,
    {- | stores a mapping from the ATP compliant
    labels to the original labels for all goals -}
    namesMap :: GenericGoalNameMap,
    -- | list of all goals
    goalsList :: [AS_Anno.Named sentence],
    -- | logical part without theorems
    proverState :: pst
  }

{- |
  Initialising the specific prover state containing logical part.
-}
type InitialProverState sign sentence morphism pst =
  sign -> [AS_Anno.Named sentence] -> [FreeDefMorphism sentence morphism] -> pst
type TransSenName = String -> String

{- |
  Creates an initial GenericState around a Theory.
-}
initialGenericState
    :: (Ord sentence, Ord proof_tree)
    => String -- ^ name of the prover
    -> InitialProverState sign sentence morphism pst
    -> TransSenName
    -> Theory sign sentence proof_tree
    -> [FreeDefMorphism sentence morphism] -- ^ freeness constraints
    -> proof_tree -- ^ initial empty proof_tree
    -> GenericState sign sentence proof_tree pst
initialGenericState prName ips trSenName th freedefs pt =
    GenericState {currentGoal = Nothing,
                  currentProofTree = pt,
                  configsMap = Map.fromList $
                               map (\ g ->
                                        let gName = AS_Anno.senAttr g
                                            ec = emptyConfig prName gName pt
                                        in (gName, ec {proofStatus =
                       updateTacticScript (proofStatus ec) gName}))
                                   goals,
                  namesMap = collectNameMapping nSens oSens',
                  goalsList = goals,
                  proverState = ips sign oSens' freedefs
                 }
    where Theory sign oSens = th
          {- Search in list of ProofStatus for first occurence of an Open goal
          with non-empty TacticScript and update TacticScript if found. -}
          updateTacticScript prStat gn =
            maybe prStat
                  (\ senSt ->
                    let validThmStatus = filter (\ tStatus ->
                            isOpenGoal (goalStatus tStatus) &&
                            tacticScript tStatus /= TacticScript "")
                                                $ thmStatus senSt
                    in if null validThmStatus
                          then prStat
                          else prStat { tacticScript = tacticScript
                                                       $ head validThmStatus })
                  $ OMap.lookup gn oSens
          oSens' = toNamedList oSens
          nSens = disambiguateSens Set.empty $ prepareSenNames trSenName oSens'
          goals = filter (not . AS_Anno.isAxiom) nSens

{- | applies the recorded name mapping (in the state) of prover
  specific names to the original names to the list of ProofStatus
  (the name of the goal and the names of used axioms are translated);
  additionally the axioms generated from typing information are
  removed and warnings are generated. -}

revertRenamingOfLabels :: (Ord sentence, Ord proof_tree) =>
                           GenericState sign sentence proof_tree pst
                        -> [ProofStatus proof_tree]
                        -> Result [ProofStatus proof_tree]
revertRenamingOfLabels st = foldM transNames []
    where trN x' = Map.findWithDefault
                      (error ("GenericATPState: Lookup of name failed: (2) " ++
                              "should not happen \"" ++ x' ++ "\""))
                      x' (namesMap st)
          transNames tr_pStats pStat =
              do uAxs <- foldM fil [] $ reverse $ usedAxioms pStat
                 return ((pStat { goalName = trN $ goalName pStat
                                , usedAxioms = uAxs }) : tr_pStats)
           where fil axs ax =
                  maybe (appendDiags [Diag Warning
                                          ("by interface to " ++
                                           usedProver pStat ++
                                           ": unknown axiom \"" ++ ax ++
                                           "\" omitted from list of used " ++
                                           "axioms of goal \"" ++
                                           trN (goalName pStat) ++ "\"")
                                          nullRange]
                         >> return axs)
                        (return . (: axs))
                       (Map.lookup ax (namesMap st))

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
  pst -- prover state containing logical part
  -> GenericConfig proof_tree -- configuration to use
  -> Bool -- True means save problem file
  -> String -- name of the theory in the DevGraph
  -> AS_Anno.Named sentence -- goal to prove
  -> IO (ATPRetval, GenericConfig proof_tree) {- (retval, configuration with
                                                   proofStatus and complete
                                                   output) -}

{- |
  Prover specific functions
-}
data ATPFunctions sign sentence morphism proof_tree pst = ATPFunctions {
    -- | initial prover specific state
    initialProverState :: InitialProverState sign sentence morphism pst,
    -- | prover specific translation of goal name
    atpTransSenName :: TransSenName,
    -- | inserts a goal into prover state
    atpInsertSentence :: pst -> AS_Anno.Named sentence -> pst,
    -- | output of a goal in a prover specific format
    goalOutput :: pst -> AS_Anno.Named sentence -> [String] -> IO String,
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
  Tactic script implementation for ATPs. Read and show functions are derived.
-}
data ATPTacticScript = ATPTacticScript
    { tsTimeLimit :: Int, -- ^ used time limit
      tsExtraOpts :: [String] -- ^ used extra options (if any)
    } deriving (Eq, Ord, Show, Read)

{- |
  Default time limit for the GUI mode prover in seconds.
-}
guiDefaultTimeLimit :: Int
guiDefaultTimeLimit = 10

{- |
  Returns the time limit from GenericConfig if available. Otherwise
  guiDefaultTimeLimit is returned.
-}
configTimeLimit :: GenericConfig proof_tree -> Int
configTimeLimit = fromMaybe guiDefaultTimeLimit . timeLimit

{- |
  Parses a given default tactic script into a
  'Interfaces.GenericATPState.ATPTacticScript' if possible. Otherwise a default
  prover's tactic script is returned.
-}
parseTacticScript
    :: Int {- ^ default time limit (standard:
           'Proofs.BatchProcessing.batchTimeLimit') -}
    -> [String] -- ^ default extra options (prover specific)
    -> TacticScript
    -> ATPTacticScript
parseTacticScript tLimit extOpts (TacticScript ts) =
    let defl = ATPTacticScript
          { tsTimeLimit = tLimit
          , tsExtraOpts = extOpts }
    in case readMaybe ts of
         Nothing -> fromMaybe defl $ readMaybe ts
         Just tl -> defl { tsTimeLimit = tl }

{- |
  Pretty printing of prover configuration.
-}
printCfgText :: Map.Map ATPIdentifier (GenericConfig proof_tree)
             -> Doc -- ^ prover configuration
printCfgText mp = text "* Configuration *" $+$ dc
             $++$ text "* Results *" $+$ dr
  where
  (dc, dr) = Map.foldWithKey (\ k cfg (dCfg, dRes) ->
      let r = proofStatus cfg
      in
      (quotes (text k) <+> equals <+> specBraces (
          text "goalStatus" <+> equals <+>
                            (text . show . goalStatus) r <> comma
          $+$ text "timeLimitExceeded" <+> equals <+>
                            (text . show . timeLimitExceeded) cfg <> comma
          $+$ text "timeUsed" <+> equals <+>
                            (text . show . timeUsed) cfg
          $+$ text "tacticScript" <+> equals <+>
                            (text . show . tacticScript) r
          ) $+$ dCfg,
       text "Output of goal" <+> quotes (text k) <> colon
            $+$ vcat (map text $ resultOutput cfg)
          $++$ dRes))
    (empty, empty) mp

-- | Converts a thrown exception into an ATP result (ATPRetval and proof tree).
excepToATPResult
  :: String -- ^ name of running prover
  -> String -- ^ goal name to prove
  -> Exception.SomeException -- ^ occured exception
  -> IO (ATPRetval, GenericConfig ProofTree)
     -- ^ (retval, configuration with proof status and complete output)
excepToATPResult prName nGoalName excep = do
  let emptyCfg = emptyConfig prName nGoalName emptyProofTree
  return $ case Exception.fromException excep of
    {- this is supposed to distinguish "fd ... vanished"
    errors from other exceptions -}
    Just e ->
        (ATPError $ "Internal error communicating with " ++ prName ++ ".\n"
         ++ show (e :: Exception.IOException), emptyCfg)
    Nothing -> case Exception.fromException excep of
      Just Exception.ThreadKilled -> (ATPBatchStopped, emptyCfg)
      _ ->
        (ATPError ("Error running " ++ prName ++ ".\n" ++ show excep), emptyCfg)
