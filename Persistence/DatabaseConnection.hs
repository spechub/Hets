{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}

-- MySQL is dactivated. To activate it,
--   * uncomment the import of the MySQL module in
--     Persistence/DatabaseConnection.hs
--   * and switch the "mysql" and "mysql2" cases in `getConnection` with the
--     commented out code underneath them in Persistence/DatabaseConnection.hs.
module Persistence.DatabaseConnection (getConnection) where

import Persistence.DBConfig

import qualified Persistence.SQLite as SQLite
-- #### Deactivate MySQL
-- MySQL support is deactivated because it requires users to install MySQL even
-- if they want to use SQLite or PostgreSQL.
-- import qualified Persistence.MySQL as MySQL
-- #### /Deactivate MySQL
#ifndef UNI_PACKAGE
import qualified Persistence.PostgreSQL as PSQL
#endif

import Control.Monad.IO.Class
import Control.Monad.Trans.Control
import Control.Monad.Logger

import Data.Maybe (fromMaybe)
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
  -- #### Deactivate MySQL
  Just "mysql" -> fail mySQLErrorMessage
  Just "mysql2" -> fail mySQLErrorMessage
  -- #### /Deactivate MySQL
  -- #### Activate MySQL
  -- Just "mysql" -> return $ MySQL.connection dbConfig $
  --                   fromMaybe defaultPoolSize $ pool dbConfig
  -- Just "mysql" -> return $ MySQL.connection dbConfig $
  --                   fromMaybe defaultPoolSize $ pool dbConfig
  -- #### /Activate MySQL
#ifdef UNI_PACKAGE
  Just "postgresql" -> fail postgreSQLErrorMessage
#else
  Just "postgresql" -> return $ PSQL.connection dbConfig $
                         fromMaybe defaultPoolSize $ pool dbConfig
#endif
  Just "sqlite" -> return $ SQLite.connection dbConfig $
                     fromMaybe defaultPoolSize $ pool dbConfig
  Just "sqlite3" -> return $ SQLite.connection dbConfig $
                      fromMaybe defaultPoolSize $ pool dbConfig
  _ -> fail ("Persistence.Database: No database adapter specified "
               ++ "or adapter unsupported.")
  where
    mySQLErrorMessage = "MySQL support is deactivated. If you need it, please let us know by filing an issue at https://github.com/spechub/Hets or write an email to hets-devel@informatik.uni-bremen.de"
#ifdef UNI_PACKAGE
    postgreSQLErrorMessage = "PostgreSQL support is deactivated. If you need it, please use the package hets-server instead of hets-desktop."
#endif
