{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result where

import PGIP.GraphQL.Result.DGraph
import PGIP.GraphQL.Result.OMS
import PGIP.GraphQL.Result.Serialization
import PGIP.GraphQL.Result.Signature
import PGIP.GraphQL.Result.SignatureMorphism

import Common.Json (ppJson, asJson)

import Data.Data

data Result = DGraphResult DGraph
            | OMSResult OMS
            | SerializationResult Serialization
            | SignatureResult Signature
            | SignatureMorphismResult SignatureMorphism
              deriving (Show, Typeable, Data)

toJson :: Result -> String
toJson result = case result of
  DGraphResult dgraph -> ppJson $ asJson dgraph
  OMSResult oms_ -> ppJson $ asJson oms_
  SerializationResult serialization_ -> ppJson $ asJson serialization_
  SignatureResult signature_ -> ppJson $ asJson signature_
  SignatureMorphismResult signatureMorphism -> ppJson $ asJson signatureMorphism
