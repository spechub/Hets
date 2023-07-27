{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.LogicMapping where

import PGIP.GraphQL.Result.StringReference
import PGIP.GraphQL.Result.LanguageMapping

import Data.Data

data LogicMapping = LogicMapping { id :: String
                                 , languageMapping :: LanguageMapping
                                 , source :: StringReference
                                 , target :: StringReference
                                 } deriving (Show, Typeable, Data)
