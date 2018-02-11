{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.LocIdReference where

import Data.Data

newtype LocIdReference = LocIdReference { locId :: String
                                        } deriving (Show, Typeable, Data)
