{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.ReasoningAttempt where

import PGIP.GraphQL.Result.Action
import PGIP.GraphQL.Result.Reasoner
import PGIP.GraphQL.Result.ReasonerConfiguration
import PGIP.GraphQL.Result.ReasonerOutput

import Data.Data

data ReasoningAttempt =
  ReasoningAttempt { action :: Action
                   , reasonerConfiguration :: ReasonerConfiguration
                   , reasonerOutput :: Maybe ReasonerOutput
                   , reasoningStatus :: String
                   , timeTaken :: Maybe Int
                   , usedReasoner :: Maybe Reasoner
                   } deriving (Show, Typeable, Data)
