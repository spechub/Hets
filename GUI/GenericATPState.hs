{- |
Module      :  GenericATPState.hs
Description :  Help functions for GUI.GenericATP
Copyright   :  (c) Klaus Lüttich, Rainer Grabbe, Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rainer25@tzi.de
Stability   :  not yet runnable
Portability :  ?

Help functions for GUI.GenericATP


-}

module GUI.GenericATPState where



-- importing some modules...
import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Lib.Map as Map

import Logic.Prover




data GenericConfig proof_tree = GenericConfig { 
    -- | time limit in seconds passed 
    -- to SPASS via -TimeLimit. Default will be used if Nothing.
    timeLimit :: Maybe Int,
    -- | True if timelimit exceed during last prover run
    timeLimitExceeded :: Bool,
    -- | extra options passed verbatimely to SPASS. 
    -- -DocProof, -Stdin, and -TimeLimit will be overridden.
    extraOpts :: [String],
    -- | Represents the result of a prover run.
    proof_status :: Proof_status proof_tree,
    resultOutput :: [String]
                               } deriving (Eq, Ord, Show)

-- type SPASSConfigsMap = Map.Map SPIdentifier SPASSConfig
type GenericConfigsMap proof_tree = Map.Map String (GenericConfig proof_tree)


-- type SPASSGoalNameMap = Map.Map String String
type GenericGoalNameMap = Map.Map String String


{--
-- experimental
data GenericState sign sentence proof_tree pst = GenericState {
-- ? just a string? or better type parameter?
    currentGoal :: Maybe String,
    -- | theory to work on
    theory :: Theory sign sentence proof_tree,
    -- | stores the prover configurations for each goal
    -- and the results retrieved by running prover for each goal
    configsMap :: GenericConfigsMap proof_tree,
    -- | stores a mapping to SPASS compliant 
    -- identifiers for all goals
-- ? just two strings in GenericGoalNameMap?
    namesMap :: GenericGoalNameMap,
    -- | list of all goals
-- ? is sentence always a term? In SPASS it is.
    goalsList :: [AS_Anno.Named sentence],
    -- | logical part without theorems
    proverState :: pst,
    batchModeIsRunning :: Bool,
    mainDestroyed :: Bool
  }
--}


type InitialProverState sign sentence pst =
      String -- ^ Theory name
      -> sign -> [AS_Anno.Named sentence] -> pst

{- |
  Creates an initial GenericState around a Theory.
-}
{--
initialGenericState :: InitialProverState sign sentence pst
                     -> sign -> [AS_Anno.Named sentence]
-- ???
                     -> GenericState sign sentence proof_tree pst
--}    

{--
initialState :: Theory Sign Sentence () -> SPASS.Prove2.State
initialState th = 
    State {currentGoal = Nothing,
           theory = th,
           configsMap = Map.fromList $
                        map (\ g -> let gName = AS_Anno.senName g
                                    in (gName, emptyConfig gName)) goals,
           namesMap = collectNameMapping nSens oSens',
           goalsList = goals,
           initialLogicalPart = foldl insertSentence 
                                      (signToSPLogicalPart sign) 
                                      (reverse axioms),
           batchModeIsRunning = False,
           mainDestroyed = False
          }
    where Theory sign oSens = th
          oSens' = toNamedList oSens
          nSens = prepareSenNames transSenName oSens'
          (axioms, goals) = partition AS_Anno.isAxiom nSens

--}
