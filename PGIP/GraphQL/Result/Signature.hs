{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.Signature where

import PGIP.GraphQL.Result.LocIdReference
import PGIP.GraphQL.Result.IdReference
import PGIP.GraphQL.Result.Symbol

import Data.Data

data Signature = Signature { id :: Int
                           , oms :: [LocIdReference]
                           , signatureMorphismsSource :: [IdReference]
                           , signatureMorphismsTarget :: [IdReference]
                           , symbols :: [Symbol]
                           } deriving (Show, Typeable, Data)
