{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.ReasonerOutput where

import Data.Data

data ReasonerOutput = ReasonerOutput { text :: String
                                     } deriving (Show, Typeable, Data)
