{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.OMSSimple where

import Data.Data

data OMSSimple = OMSSimple { description :: Maybe String
                           , displayName :: String
                           , labelHasFree :: Bool
                           , labelHasHiding :: Bool
                           , locId :: String
                           , name :: String
                           , nameExtension :: String
                           , nameExtensionIndex :: Int
                           , origin :: String
                           } deriving (Show, Typeable, Data)
