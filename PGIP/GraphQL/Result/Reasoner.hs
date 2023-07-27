{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.Reasoner where

import Data.Data

data Reasoner = Reasoner { id :: String
                         , displayName :: String
                         } deriving (Show, Typeable, Data)
