{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.Library where

import PGIP.GraphQL.Result.DocumentLink
import PGIP.GraphQL.Result.OMS

import Data.Data

data Library = Library { __typename :: String
                       , documentLinks :: [DocumentLink]
                       , oms :: [OMS]
                       } deriving (Show, Typeable, Data)
