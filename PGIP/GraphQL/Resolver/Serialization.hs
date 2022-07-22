module PGIP.GraphQL.Resolver.Serialization (resolve) where

import PGIP.GraphQL.Resolver.ToResult

import PGIP.GraphQL.Result as GraphQLResult

import PGIP.Shared

import Driver.Options
import Persistence.Database
import Persistence.Schema as DatabaseSchema

import Database.Esqueleto

import Control.Monad.IO.Class (MonadIO (..))

resolve :: HetcatsOpts -> Cache -> String -> IO (Maybe GraphQLResult.Result)
resolve opts _ idVar =
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
    (serializationEntity, languageEntity) : _ ->
        return $ Just $ GraphQLResult.SerializationResult $
          serializationToResult serializationEntity languageEntity
