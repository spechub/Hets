module PGIP.GraphQL.Resolver.Serialization (resolve) where

import PGIP.GraphQL.Resolver.Utils

import PGIP.GraphQL.Result as GraphQLResult
import PGIP.GraphQL.Result.Serialization as GraphQLResultSerialization

import PGIP.Shared

import Driver.Options
import Persistence.Database
import Persistence.Schema as DatabaseSchema

import Database.Esqueleto

import Control.Monad.IO.Class (MonadIO (..))

resolve :: HetcatsOpts -> Cache -> String -> IO (Maybe GraphQLResult.Result)
resolve opts sessionReference idVar =
  onDatabase (databaseConfig opts) $ resolveDB idVar

resolveDB :: MonadIO m => String -> DBMonad m (Maybe GraphQLResult.Result)
resolveDB idVar = do
serializationL <-
  select $ from $ \(serializations `InnerJoin` languages) -> do
    on (serializations ^. SerializationLanguageId ==. languages ^. LanguageId)
    where_ (serializations ^. SerializationSlug ==. val idVar)
    return (serializations, languages)
case serializationL of
  [] -> return Nothing
  (Entity _ serializationValue, languageEntity) : _ -> do
      let languageResult = languageEntityToLanguageResult languageEntity
      return $ Just $ GraphQLResult.SerializationResult
        GraphQLResultSerialization.Serialization
          { GraphQLResultSerialization.id = serializationSlug serializationValue
          , GraphQLResultSerialization.language = languageResult
          , GraphQLResultSerialization.name = serializationName serializationValue
          }
