{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.OMS where

import PGIP.GraphQL.Result.ConservativityStatus
import PGIP.GraphQL.Result.FileRange
import PGIP.GraphQL.Result.IdReference
import PGIP.GraphQL.Result.Language
import PGIP.GraphQL.Result.LocIdReference
import PGIP.GraphQL.Result.Logic
import PGIP.GraphQL.Result.Mapping
import PGIP.GraphQL.Result.ReasoningAttempt
import PGIP.GraphQL.Result.Sentence
import PGIP.GraphQL.Result.StringReference

import Data.Data

data OMS = OMS { id :: Int
               , conservativityStatus :: ConservativityStatus
               , consistencyCheckAttempts :: [ReasoningAttempt]
               , description :: Maybe String
               , displayName :: String
               , freeNormalForm :: Maybe LocIdReference
               , freeNormalFormSignatureMorphism :: Maybe IdReference
               , labelHasFree :: Bool
               , labelHasHiding :: Bool
               , language :: Language
               , locId :: String
               , logic :: Logic
               , mappings :: [Mapping]
               , name :: String
               , nameExtension :: String
               , nameExtensionIndex :: Int
               , nameFileRange :: Maybe FileRange
               , origin :: String
               , sentences :: [Sentence]
               , serialization :: StringReference
               , omsSignature :: IdReference
               } deriving (Show, Typeable, Data)
