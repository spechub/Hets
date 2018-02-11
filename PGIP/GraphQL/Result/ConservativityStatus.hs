{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.ConservativityStatus where

import Data.Data

data ConservativityStatus =
  ConservativityStatus { required :: String
                       , proved :: String
                       } deriving (Show, Typeable, Data)
