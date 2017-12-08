{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}

module Persistence.DynamicDatabaseConnection (getConnection) where

import Persistence.DBConfig

import qualified System.Plugins as Plugins
-- import qualified Persistence.MySQL as MySQL

import qualified Persistence.PostgreSQL as PSQL
import qualified Persistence.SQLite as SQLite

import Control.Monad.IO.Class
import Control.Monad.Trans.Control
import Control.Monad.Logger

import Data.Pool (Pool)

import Database.Persist.Sql

defaultPoolSize :: Int
defaultPoolSize = 4

getConnection :: ( BaseBackend backend ~ SqlBackend
                 , IsPersistBackend backend
                 , MonadIO m
                 , MonadBaseControl IO m
                 , MonadLogger m
                 )
              => DBConfig -> IO ((Pool backend -> m a) -> m a)
getConnection dbConfig = case adapter dbConfig of
  Just "mysql" -> loadMySQLPlugin dbConfig
  Just "mysql2" -> loadMySQLPlugin dbConfig
  Just "postgresql" -> return $ PSQL.connection dbConfig defaultPoolSize
  Just "sqlite" -> return $ SQLite.connection dbConfig defaultPoolSize
  Just "sqlite3" -> return $ SQLite.connection dbConfig defaultPoolSize
  _ -> fail ("Persistence.Database: No database adapter specified "
               ++ "or adapter unsupported.")

loadMySQLPlugin :: ( BaseBackend backend ~ SqlBackend
                   , IsPersistBackend backend
                   , MonadIO m
                   , MonadBaseControl IO m
                   , MonadLogger m
                   )
                => DBConfig -> IO ((Pool backend -> m a) -> m a)
loadMySQLPlugin dbConfig = do
  mv <- Plugins.load_ "Persistence/MySQL.o" ["."] "connection"
  case mv of
    Plugins.LoadFailure _ ->
      fail "Persistence.Database: Failed to load MySQL adapter."
    Plugins.LoadSuccess _ connection ->
      return $ connection dbConfig defaultPoolSize
