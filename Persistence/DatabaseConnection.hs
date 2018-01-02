{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}

module Persistence.DatabaseConnection (getConnection) where

import Persistence.DBConfig

import qualified Persistence.SQLite as SQLite
-- MySQL support is deactivated because it requires users to install MySQL even
-- if they want to use SQLite or PostgreSQL.
-- import qualified Persistence.MySQL as MySQL
#ifndef UNI_PACKAGE
import qualified Persistence.PostgreSQL as PSQL
#endif

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
  Just "mysql" -> fail mySQLErrorMessage
  Just "mysql2" -> fail mySQLErrorMessage
  -- Just "mysql" -> return $ MySQL.connection dbConfig defaultPoolSize
  -- Just "mysql" -> return $ MySQL.connection dbConfig defaultPoolSize
#ifdef UNI_PACKAGE
  Just "postgresql" -> fail postgreSQLErrorMessage
#else
  Just "postgresql" -> return $ PSQL.connection dbConfig defaultPoolSize
#endif
  Just "sqlite" -> return $ SQLite.connection dbConfig defaultPoolSize
  Just "sqlite3" -> return $ SQLite.connection dbConfig defaultPoolSize
  _ -> fail ("Persistence.Database: No database adapter specified "
               ++ "or adapter unsupported.")
  where
    mySQLErrorMessage = "MySQL support is deactivated. If you need it, please let us know by filing an issue at https://github.com/spechub/Hets or write an email to hets-devel@informatik.uni-bremen.de"
#ifdef UNI_PACKAGE
    postgreSQLErrorMessage = "PostgreSQL support is deactivated. If you need it, please use the package hets-server instead of hets-desktop."
#endif
