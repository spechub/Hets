{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.Serialization where

import PGIP.GraphQL.Result.Language

import Data.Data

data Serialization = Serialization { id :: String
                                   , language :: Language
                                   , name :: String
                                   } deriving (Show, Typeable, Data)
