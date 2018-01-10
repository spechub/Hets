{-# LANGUAGE OverloadedStrings #-}

module PGIP.GraphQL.Resolver (resolve) where

import PGIP.GraphQL.Result as GraphQLResult
import PGIP.GraphQL.Result.Language
import PGIP.GraphQL.Result.Serialization as GraphQLResultSerialization

import PGIP.Shared

import Driver.Options

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text

resolve :: HetcatsOpts -> Cache -> Text -> Map Text Text -> IO String
resolve opts sessionReference query variables = do
  queryType <- determineQueryType query
  case queryType of
    QTSerialization -> return $ GraphQLResult.toJson $ SerializationResult $
      GraphQLResultSerialization.Serialization "serId" (Language "langId" "langName" "langDescr") "serName"
    QTDGraph -> undefined
    QTOMS -> undefined
    QTSignature -> case Map.lookup "id" variables of
      Nothing -> fail "Signature query: Variable \"id\" not provided."
      Just idVar -> resolveSignature opts sessionReference $ read $ Text.unpack idVar
    QTSignatureMorphism -> undefined

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


resolveSignature :: HetcatsOpts -> Cache -> Int -> IO String
resolveSignature opts sessionReference idVar = undefined
