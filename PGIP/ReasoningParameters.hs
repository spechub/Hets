{-# LANGUAGE DeriveGeneric #-}

module PGIP.ReasoningParameters where

import Data.Aeson
import GHC.Generics

configuredReasoner :: ReasoningParameters -> Maybe String
configuredReasoner reasoningParameters =
  reasoner $ reasonerConfiguration reasoningParameters

data ReasoningParameters =
  ReasoningParameters { reasonerConfiguration :: ReasonerConfiguration
                      , premiseSelection :: Maybe PremiseSelection
                      } deriving (Show, Generic)
instance FromJSON ReasoningParameters

data ReasonerConfiguration = ReasonerConfiguration { timeLimit :: Int
                                                   , reasoner :: Maybe String
                                                   } deriving (Show, Generic)
instance FromJSON ReasonerConfiguration

data PremiseSelection = PremiseSelection { kind :: String
                                         , manualPremises :: Maybe [String]
                                         , sineDepthLimit :: Maybe Int
                                         , sineTolerance :: Maybe Double
                                         , sinePremiseNumberLimit :: Maybe Int
                                         }
                        deriving (Show, Generic)
instance FromJSON PremiseSelection
