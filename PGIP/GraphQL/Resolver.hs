module PGIP.GraphQL.Resolver (resolve) where

import PGIP.GraphQL.Result as GraphQLResult
import PGIP.GraphQL.Result.Language
import PGIP.GraphQL.Result.Serialization as GraphQLResultSerialization

import PGIP.GraphQL.Shared

import PGIP.Shared

import Driver.Options

import Data.Map (Map)
import Data.Text (Text)

resolve :: HetcatsOpts -> Cache -> QueryType -> Text -> Map Text Text -> IO String
resolve opts sessionReference queryType query variables =
  return $ GraphQLResult.toJson $ GraphQLResult.Foo $
    GraphQLResultSerialization.Serialization "serId" (Language "langId" "langName" "langDescr") "serName"
