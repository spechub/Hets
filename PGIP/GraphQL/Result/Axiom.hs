{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.Axiom where

import PGIP.GraphQL.Result.FileRange
import PGIP.GraphQL.Result.Symbol

import Data.Data

data Axiom = Axiom { __typename :: String
                   , fileRange :: Maybe FileRange
                   , locId :: String
                   , name :: String
                   , symbols :: [Symbol]
                   , text :: String
                   } deriving (Show, Typeable, Data)
