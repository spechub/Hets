{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result where

import PGIP.GraphQL.Result.DGraph
import PGIP.GraphQL.Result.OMS
import PGIP.GraphQL.Result.Serialization
import PGIP.GraphQL.Result.Signature
import PGIP.GraphQL.Result.SignatureMorphism

import Common.Json (ppJson, asJson)

import Data.Data

data Result = SerializationResult Serialization
            | SignatureResult Signature
            | SignatureMorphismResult SignatureMorphism
              deriving (Show, Typeable, Data)

toJson :: Result -> String
toJson result = case result of
  SerializationResult serializationVar -> ppJson $ asJson serializationVar
  SignatureResult signatureVar -> ppJson $ asJson signatureVar
  SignatureMorphismResult signatureMorphismVar -> ppJson $ asJson signatureMorphismVar
