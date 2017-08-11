{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}

module Persistence.Database where

import Persistence.DBConfig
import qualified Persistence.PostgreSQL as PSQL

import Control.Monad.IO.Class
import Control.Monad.Trans.Control
import Control.Monad.Trans.Reader
import Control.Monad.Logger

import Data.Maybe
import Database.Persist.Postgresql
import Database.Persist.Sqlite
import Data.Text (pack)

onDatabase :: (BaseBackend backend ~ SqlBackend,
               IsPersistBackend backend, MonadIO m,
               MonadBaseControl IO m)
           => DBConfig
           -> ReaderT backend (NoLoggingT m) a
           -> m a
onDatabase dbConfig =
  let connection = case adapter dbConfig of
        Just "postgresql" ->
          withPostgresqlPool (PSQL.connectionString dbConfig) $
            fromMaybe defaultPoolSize $ pool dbConfig
        Just "sqlite" ->
          withSqlitePool (pack $ database dbConfig) defaultPoolSize
        _ -> fail ("Persistence.Database: No database adapter specified "
                     ++ "or adapter unsupported.")
  in runNoLoggingT . connection . runSqlPool

defaultPoolSize :: Int
defaultPoolSize = 4
