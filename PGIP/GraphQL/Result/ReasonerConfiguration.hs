{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.ReasonerConfiguration where

import PGIP.GraphQL.Result.Reasoner
import PGIP.GraphQL.Result.PremiseSelection

import Data.Data

data ReasonerConfiguration =
  ReasonerConfiguration { configuredReasoner :: Maybe Reasoner
                        , id :: Int
                        , premiseSelections :: [PremiseSelection]
                        , timeLimit :: Maybe Int
                        } deriving (Show, Typeable, Data)
