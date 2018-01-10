{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.SignatureMorphismReference where

import Data.Data

newtype SignatureMorphismReference =
  SignatureMorphismReference { id :: Int } deriving (Show, Typeable, Data)

