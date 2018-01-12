{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.Mapping where

import PGIP.GraphQL.Result.ConservativityStatus
import PGIP.GraphQL.Result.IdReference
import PGIP.GraphQL.Result.Language
import PGIP.GraphQL.Result.LocIdReference

import Data.Data

data Mapping = Mapping { conservativityStatus :: Maybe ConservativityStatus
                       , displayName :: String
                       , freenessParameterOMS :: Maybe LocIdReference
                       , freenessParameterLanguage :: Maybe Language
                       , locId :: String
                       , name :: String
                       , origin :: String
                       , pending :: Bool
                       , signatureMorphism :: IdReference
                       , source :: LocIdReference
                       , target :: LocIdReference
                       , mappingType :: String
                       } deriving (Show, Typeable, Data)
