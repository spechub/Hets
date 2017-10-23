{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}

module Persistence.Database where

import Persistence.DBConfig
import Persistence.Schema
import qualified Persistence.MySQL as MySQL
import qualified Persistence.PostgreSQL as PSQL

import Control.Monad (when)
import Control.Monad.IO.Class
import Control.Monad.Trans.Control
import Control.Monad.Trans.Reader
import Control.Monad.Logger

import Data.Maybe
import Database.Persist.MySQL
import Database.Persist.Postgresql
import Database.Persist.Sqlite
import Data.Text (pack)

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
       when (doMigrate dbConfig) $ runMigration migrateAll
       f

defaultPoolSize :: Int
defaultPoolSize = 4
