{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.Library where

import PGIP.GraphQL.Result.DocumentLink
import PGIP.GraphQL.Result.OMSSimple

import Data.Data

data Library = Library { __typename :: String
                       , displayName :: String
                       , locId :: String
                       , name :: String
                       , version :: Maybe String
                       , documentLinksSource :: [DocumentLink]
                       , documentLinksTarget :: [DocumentLink]
                       , omsList :: [OMSSimple]
                       } deriving (Show, Typeable, Data)
