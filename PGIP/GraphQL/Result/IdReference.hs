{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.IdReference where

import Data.Data

newtype IdReference = IdReference { id :: String
                                  } deriving (Show, Typeable, Data)
