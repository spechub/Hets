{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.StringReference where

import Data.Data

newtype StringReference = StringReference { id :: String
                                          } deriving (Show, Typeable, Data)
