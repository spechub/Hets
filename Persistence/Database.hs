{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE ScopedTypeVariables        #-}

module Persistence.Database where

import Persistence.DBConfig
import Persistence.Schema
import qualified Persistence.MySQL as MySQL
import qualified Persistence.PostgreSQL as PSQL

import Control.Exception.Lifted
import Control.Monad (when)
import Control.Monad.IO.Class
import Control.Monad.Trans.Control
import Control.Monad.Trans.Reader
import Control.Monad.Logger

import Data.List (intercalate, isInfixOf)
import Data.Maybe
import Database.Persist.MySQL
import Database.Persist.Postgresql
import Database.Persist.Sqlite
import Data.Text (Text, pack)

type DBMonad m a = ReaderT SqlBackend m a

onDatabase :: ( MonadIO m
              , MonadBaseControl IO m
              )
           => DBConfig
           -> DBMonad (NoLoggingT m) a
           -> m a
onDatabase dbConfig f =
  let connection = case adapter dbConfig of
        Just "mysql" ->
          withMySQLPool (MySQL.connectionInfo dbConfig) $
            fromMaybe defaultPoolSize $ pool dbConfig
        Just "mysql2" ->
          withMySQLPool (MySQL.connectionInfo dbConfig) $
            fromMaybe defaultPoolSize $ pool dbConfig
        Just "postgresql" ->
          withPostgresqlPool (PSQL.connectionString dbConfig) $
            fromMaybe defaultPoolSize $ pool dbConfig
        Just "sqlite" ->
          withSqlitePool (pack $ database dbConfig) defaultPoolSize
        Just "sqlite3" ->
          withSqlitePool (pack $ database dbConfig) defaultPoolSize
        _ -> fail ("Persistence.Database: No database adapter specified "
                     ++ "or adapter unsupported.")
  in runNoLoggingT $ connection $ runSqlPool $ do
       runFullMigrationSet dbConfig
       f

defaultPoolSize :: Int
defaultPoolSize = 4

runFullMigrationSet :: forall m . ( MonadBaseControl IO m
                                  , MonadIO m
                                  )
                    => DBConfig -> DBMonad m ()
runFullMigrationSet dbConfig =
  when (doMigrate dbConfig) $ do
    runMigrationSilent migrateAll
    mapM_ (handle ignoreIndexExistsError . runRawSql) $ indexesSQL dbConfig
  where
    runRawSql :: MonadIO m => String -> DBMonad m [Single (Maybe Text)]
    runRawSql sql =
      let query = pack $ if isMySql dbConfig
                         then sql
                         else sql ++ " SELECT ('dummy');"
      in  rawSql query []

    ignoreIndexExistsError :: MonadIO m
                           => SomeException -> DBMonad m [Single (Maybe Text)]
    ignoreIndexExistsError exception =
      let message = show exception in
      if isMySql dbConfig && ("'ix_" `isInfixOf` message)
      then return []
      else fail message

indexesSQL :: DBConfig -> [String]
indexesSQL dbConfig =
  map sqlString
    [ ("languages", ["slug"])
    , ("logics", ["slug"])
    , ("language_mappings", ["source_id", "target_id"])
    , ("logic_mappings", ["language_mapping_id", "slug"])
    , ("signature_morphisms", ["logic_mapping_id", "source_id", "target_id"])
    , ("symbol_mappings", ["signature_morphism_id", "source_id", "target_id"])
    ]
  where
    sqlString :: (String, [String]) -> String
    sqlString (table, columns) =
      let indexName = "ix_" ++ table ++ "__" ++ intercalate "__" columns
          indexNameMySql = take 64 indexName
          indexedColumns = intercalate ", " columns
          mysqlString =
            "CREATE INDEX " ++ indexNameMySql ++ " ON " ++ table ++ ""
            ++ "(" ++ indexedColumns ++ ");"
          genericString =
            "CREATE INDEX IF NOT EXISTS " ++ indexName ++ " ON " ++ table ++ ""
            ++ "(" ++ indexedColumns ++ ");"
      in  case adapter dbConfig of
            Just "mysql" -> mysqlString
            Just "mysql2" -> mysqlString
            Just "postgresql" -> genericString
            Just "sqlite" -> genericString
            Just "sqlite3" -> genericString
            _ -> genericString
