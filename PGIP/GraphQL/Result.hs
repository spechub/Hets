{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result where

import PGIP.GraphQL.Result.Language
import PGIP.GraphQL.Result.Serialization

import Common.Json (ppJson, asJson)

import Data.Data

data Result = Foo Serialization
            | Bar Serialization
              deriving (Show, Typeable, Data)

toJson :: Result -> String
toJson result = case result of
  Foo serialization -> ppJson $ asJson serialization
  Bar serialization -> ppJson $ asJson serialization
