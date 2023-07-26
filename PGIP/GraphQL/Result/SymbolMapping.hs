{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.SymbolMapping where

import PGIP.GraphQL.Result.Symbol

import Data.Data

data SymbolMapping = SymbolMapping { source :: Symbol
                                   , target :: Symbol
                                   } deriving (Show, Typeable, Data)
