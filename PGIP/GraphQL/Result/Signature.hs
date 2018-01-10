{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.Signature where

import PGIP.GraphQL.Result.LocIdReference
import PGIP.GraphQL.Result.SignatureMorphismReference
import PGIP.GraphQL.Result.Symbol

import Data.Data

data Signature = Signature { id :: Int
                           , oms :: [LocIdReference]
                           , signatureMorphismsSource :: [SignatureMorphismReference]
                           , signatureMorphismsTarget :: [SignatureMorphismReference]
                           , symbols :: [Symbol]
                           } deriving (Show, Typeable, Data)
