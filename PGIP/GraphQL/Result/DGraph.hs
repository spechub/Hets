{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.DGraph where

import PGIP.GraphQL.Result.Library
import PGIP.GraphQL.Result.NativeDocument

import Data.Data

data DGraph = DGLibrary Library | DGNativeDocument NativeDocument
              deriving (Show, Typeable, Data)
