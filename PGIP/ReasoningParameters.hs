{-# LANGUAGE DeriveGeneric #-}

module PGIP.ReasoningParameters where

import PGIP.Shared (ProverMode)

import Logic.Comorphism (AnyComorphism)
import Logic.Grothendieck (G_sublogics)
import Proofs.AbstractState (ProverOrConsChecker)
import Static.DevGraph (DGNodeLab)
import Static.GTheory (G_theory)
import qualified Persistence.Schema as DatabaseSchema

import Data.Aeson
import GHC.Generics

data ReasoningParameters =
  ReasoningParameters { goals :: [GoalConfig]
                      , format :: Maybe String
                      } deriving (Show, Eq, Generic)
instance FromJSON ReasoningParameters

data GoalConfig = GoalConfig { node :: String
                             , conjecture :: Maybe String -- required on "prove", must be omitted on "consistency-check"
                             , reasonerConfiguration :: ReasonerConfiguration
                             , premiseSelection :: Maybe PremiseSelection -- ignored on "consistency-check"
                             , translation :: Maybe String
                             , useTheorems :: Maybe Bool -- ignored on "consistency-check"
                             , printDetails :: Maybe Bool
                             , printProof :: Maybe Bool
                             } deriving (Show, Eq, Generic)
instance FromJSON GoalConfig

data ReasonerConfiguration = ReasonerConfiguration { timeLimit :: Int
                                                   , reasoner :: Maybe String
                                                   } deriving (Show, Eq, Generic)
instance FromJSON ReasonerConfiguration

data PremiseSelection = PremiseSelection { kind :: String -- One of "Manual", "SInE" (case-insensitive)
                                         , manualPremises :: Maybe [String]
                                         , sineDepthLimit :: Maybe Int
                                         , sineTolerance :: Maybe Double
                                         , sinePremiseNumberLimit :: Maybe Int
                                         }
                        deriving (Show, Eq, Generic)
instance FromJSON PremiseSelection

type ReasoningCacheE = [Either String ReasoningCacheGoal]
type ReasoningCache = [ReasoningCacheGoal]
data ReasoningCacheGoal = ReasoningCacheGoal
  { rceProverMode :: ProverMode
  , rceNode :: (Int, DGNodeLab)
  , rceGoalNameM :: Maybe String -- "Nothing" iff doing consistency-checking
  , rceGoalConfig :: GoalConfig
  , rceGTheory :: G_theory
  , rceGSublogic :: G_sublogics
  , rceReasoner :: ProverOrConsChecker
  , rceComorphism :: AnyComorphism
  , rceTimeLimit :: Int
  , rceUseDatabase :: Bool
  , rceReasonerConfigurationKeyM :: Maybe DatabaseSchema.ReasonerConfigurationId -- made "Just" in the setupReasoning step if a database is used
  , rceReasoningAttemptKeyM :: Maybe DatabaseSchema.ReasoningAttemptId -- made "Just" in the preprocessReasoning step if a database is used
  } deriving Show
