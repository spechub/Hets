{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.NativeDocument where

import PGIP.GraphQL.Result.DocumentLink
import PGIP.GraphQL.Result.OMSSimple

import Data.Data

data NativeDocument = NativeDocument { __typename :: String
                                     , displayName :: String
                                     , locId :: String
                                     , name :: String
                                     , version :: Maybe String
                                     , documentLinksSource :: [DocumentLink]
                                     , documentLinksTarget :: [DocumentLink]
                                     , oms :: OMSSimple
                                     } deriving (Show, Typeable, Data)
