{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.Language where

import Data.Data

data Language = Language { id :: String
                         , name :: String
                         , description :: String
                         } deriving (Show, Typeable, Data)
