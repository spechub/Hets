{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.FileRange where

import Data.Data

data FileRange = FileRange { startLine :: Int
                           , startColumn :: Int
                           , endLine :: Int
                           , endColumn :: Int
                           , path :: String
                           } deriving (Show, Typeable, Data)
