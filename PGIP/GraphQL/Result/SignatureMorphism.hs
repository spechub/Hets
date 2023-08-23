{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.SignatureMorphism where

import PGIP.GraphQL.Result.IdReference
import PGIP.GraphQL.Result.LogicMapping
import PGIP.GraphQL.Result.Mapping
import PGIP.GraphQL.Result.SymbolMapping

import Data.Data

data SignatureMorphism =
  SignatureMorphism { id :: Int
                    , logicMapping :: LogicMapping
                    , mappings :: [Mapping]
                    , source :: IdReference
                    , symbolMappings :: [SymbolMapping]
                    , target :: IdReference
                    } deriving (Show, Typeable, Data)
