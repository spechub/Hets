{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE ScopedTypeVariables        #-}

module Persistence.SQLite (connection) where

import Persistence.DBConfig

import qualified Data.ByteString.Char8 as BS
import Data.Maybe
import Data.Text (Text, pack)
import Database.Persist.Sqlite


connection dbConfig defaultPoolSize =
  withSqlitePool (pack $ database dbConfig) $
    fromMaybe defaultPoolSize $ pool dbConfig
