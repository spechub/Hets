{-# LANGUAGE OverloadedStrings #-}

module PGIP.GraphQL.Resolver (resolve) where

import qualified PGIP.GraphQL.Resolver.Serialization as SerializationResolver
import qualified PGIP.GraphQL.Resolver.Signature as SignatureResolver
import qualified PGIP.GraphQL.Resolver.SignatureMorphism as SignatureMorphismResolver

import PGIP.GraphQL.Result as GraphQLResult

import PGIP.Shared

import Driver.Options

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text

resolve :: HetcatsOpts -> Cache -> Text -> Map Text Text -> IO String
resolve opts sessionReference query variables = do
  queryType <- determineQueryType query
  resultM <- case queryType of
    QTSerialization -> case Map.lookup "id" variables of
      Nothing -> fail "Serialization query: Variable \"id\" not provided."
      Just idVar -> SerializationResolver.resolve opts sessionReference $ Text.unpack idVar
    QTDGraph -> undefined
    QTOMS -> undefined
    QTSignature -> case Map.lookup "id" variables of
      Nothing -> fail "Signature query: Variable \"id\" not provided."
      Just idVar -> SignatureResolver.resolve opts sessionReference $ read $ Text.unpack idVar
    QTSignatureMorphism -> case Map.lookup "id" variables of
      Nothing -> fail "SignatureMorphism query: Variable \"id\" not provided."
      Just idVar -> SignatureMorphismResolver.resolve opts sessionReference $ read $ Text.unpack idVar
  return $ resultToResponse queryType resultM

resultToResponse :: QueryType -> Maybe GraphQLResult.Result -> String
resultToResponse queryType = maybe noData (responseData queryType . GraphQLResult.toJson)

responseData :: QueryType -> String -> String
responseData queryType json =
  let keyword = case queryType of
        QTDGraph -> "dgraph"
        QTOMS -> "oms"
        QTSerialization -> "serialization"
        QTSignature -> "signature"
        QTSignatureMorphism -> "signatureMorphism"
  in  "{\"data\": {\n  \"" ++ keyword ++ "\":" ++ json ++ "}}"

noData :: String
noData = "{\"data\": null}"

data QueryType = QTDGraph | QTOMS | QTSerialization | QTSignature | QTSignatureMorphism
                 deriving Show

determineQueryType :: Text -> IO QueryType
determineQueryType queryArg
  | isQueryPrefix "query DGraph" = return QTDGraph
  | isQueryPrefix "query OMS" = return QTOMS
  | isQueryPrefix "query Serialization" = return QTSerialization
  | isQueryPrefix "query SignatureMorphism" = return QTSignatureMorphism
  | isQueryPrefix "query Signature" = return QTSignature
  | otherwise =
      fail ("Query not supported.\n"
            ++ "The query must begin with \"query X\", where X is one of "
            ++ "DGraph, OMS, Serialization, Signature, SignatureMorphism\n"
            ++ "This is due to a limitation of only mimicking a GraphQL API.")
  where
    isQueryPrefix :: String -> Bool
    isQueryPrefix s = Text.isPrefixOf (Text.pack s) queryArg
