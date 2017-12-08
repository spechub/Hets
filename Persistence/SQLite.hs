{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE ScopedTypeVariables        #-}

module Persistence.SQLite (connection) where

import Persistence.DBConfig

import Control.Monad.IO.Class
import Control.Monad.Trans.Control
import Control.Monad.Logger
import Data.Maybe
import Data.Pool (Pool)
import Data.Text (pack)
import Database.Persist.Sqlite


connection :: ( BaseBackend backend ~ SqlBackend
              , IsPersistBackend backend
              , MonadIO m
              , MonadBaseControl IO m
              , MonadLogger m
              )
           => DBConfig -> Int -> (Pool backend -> m a) -> m a
connection dbConfig defaultPoolSize =
  withSqlitePool (pack $ database dbConfig) $
    fromMaybe defaultPoolSize $ pool dbConfig
