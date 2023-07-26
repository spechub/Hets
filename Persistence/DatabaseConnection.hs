{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}

module Persistence.DatabaseConnection (getConnection) where

import Persistence.DBConfig

import qualified Persistence.SQLite as SQLite
#ifdef MYSQL
-- NOTE: MySQL support requires users to install MySQL even if they want to use
-- SQLite or PostgreSQL.
import qualified Persistence.MySQL as MySQL
#endif
#ifndef UNI_PACKAGE
import qualified Persistence.PostgreSQL as PSQL
#endif

import Control.Monad.IO.Class
import Control.Monad.Trans.Control
import Control.Monad.Logger
import Control.Monad.IO.Unlift
import qualified Control.Monad.Fail as Fail

import Data.Maybe (fromMaybe)
import Data.Pool (Pool)

import Database.Persist.Sql

defaultPoolSize :: Int
defaultPoolSize = 4

getConnection :: ( MonadIO m
                 , MonadBaseControl IO m
                 , MonadLogger m
                 , MonadLoggerIO m
                 , MonadUnliftIO m
                 )
              => DBConfig -> IO ((Pool SqlBackend -> m a) -> m a)
getConnection dbConfig = case adapter dbConfig of
#ifdef MYSQL
  Just "mysql" -> return $ MySQL.connection dbConfig $
                    fromMaybe defaultPoolSize $ pool dbConfig
  Just "mysql2" -> return $ MySQL.connection dbConfig $
                    fromMaybe defaultPoolSize $ pool dbConfig
#else
  Just "mysql" -> Fail.fail mySQLErrorMessage
  Just "mysql2" -> Fail.fail mySQLErrorMessage
#endif
#ifdef UNI_PACKAGE
  Just "postgresql" -> Fail.fail postgreSQLErrorMessage
#else
  Just "postgresql" -> return $ PSQL.connection dbConfig $
                         fromMaybe defaultPoolSize $ pool dbConfig
#endif
  Just "sqlite" -> return $ SQLite.connection dbConfig $
                     fromMaybe defaultPoolSize $ pool dbConfig
  Just "sqlite3" -> return $ SQLite.connection dbConfig $
                      fromMaybe defaultPoolSize $ pool dbConfig
  _ -> Fail.fail ("Persistence.Database: No database adapter specified "
               ++ "or adapter unsupported.")
  where
#ifndef MYSQL
    mySQLErrorMessage = "MySQL support is deactivated. If you need it, please use a hets-server package compiled with the mysql flag instead of hets-desktop."
#endif
#ifdef UNI_PACKAGE
    postgreSQLErrorMessage = "PostgreSQL support is deactivated. If you need it, please use the package hets-server instead of hets-desktop."
#endif
