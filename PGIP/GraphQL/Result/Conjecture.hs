{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.Conjecture where

import PGIP.GraphQL.Result.Action
import PGIP.GraphQL.Result.FileRange
import PGIP.GraphQL.Result.ReasoningAttempt
import PGIP.GraphQL.Result.Symbol

import Data.Data

data Conjecture = Conjecture { __typename :: String
                             , fileRange :: Maybe FileRange
                             , locId :: String
                             , name :: String
                             , symbols :: [Symbol]
                             , text :: String
                             , action :: Action
                             , proofAttempts :: [ReasoningAttempt]
                             , reasoningStatus :: String
                             } deriving (Show, Typeable, Data)
