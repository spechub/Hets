{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.DocumentLink where

import PGIP.GraphQL.Result.LocIdReference

import Data.Data

data DocumentLink = DocumentLink { source :: LocIdReference
                                 , target :: LocIdReference
                                 } deriving (Show, Typeable, Data)
