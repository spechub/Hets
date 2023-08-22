{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.Symbol where

import PGIP.GraphQL.Result.FileRange

import Data.Data

data Symbol = Symbol { __typename :: String
                     , fileRange :: Maybe FileRange
                     , fullName :: String
                     , kind :: String
                     , locId :: String
                     , name :: String
                     } deriving (Show, Typeable, Data)
