{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.Logic where

import Data.Data

data Logic = Logic { id :: String
                   , name :: String
                   } deriving (Show, Typeable, Data)
