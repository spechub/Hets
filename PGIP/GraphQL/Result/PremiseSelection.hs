{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.PremiseSelection where

import PGIP.GraphQL.Result.LocIdReference

import Data.Data

data PremiseSelection = PremiseSelection { selectedPremises :: [LocIdReference]
                                         } deriving (Show, Typeable, Data)
