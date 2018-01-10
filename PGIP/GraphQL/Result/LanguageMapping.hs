{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.LanguageMapping where

import PGIP.GraphQL.Result.StringReference

import Data.Data

data LanguageMapping = LanguageMapping { id :: String
                                       , source :: StringReference
                                       , target :: StringReference
                                       } deriving (Show, Typeable, Data)
