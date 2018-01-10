{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.NativeDocument where

import PGIP.GraphQL.Result.DocumentLink
import PGIP.GraphQL.Result.OMS

import Data.Data

data NativeDocument = NativeDocument { __typename :: String
                                     , documentLinks :: [DocumentLink]
                                     , oms :: OMS
                                     } deriving (Show, Typeable, Data)
