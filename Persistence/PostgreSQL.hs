{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE ScopedTypeVariables        #-}

module Persistence.PostgreSQL (connection) where

import Persistence.DBConfig

import Control.Monad.IO.Class
import Control.Monad.Trans.Control
import Control.Monad.Logger
import Control.Monad.IO.Unlift
import qualified Data.ByteString.Char8 as BS
import Data.Maybe
import Data.Pool (Pool)
import Database.Persist.Postgresql

connection :: ( MonadIO m
              , MonadBaseControl IO m
              , MonadLogger m
              , MonadUnliftIO m
              )
           => DBConfig -> Int -> (Pool SqlBackend -> m a) -> m a
connection dbConfig defaultPoolSize =
  withPostgresqlPool (connectionString dbConfig) $
    fromMaybe defaultPoolSize $ pool dbConfig

connectionString :: DBConfig -> BS.ByteString
connectionString config =
  let db = "dbname=" ++ database config
      user = fmap ("user=" ++) $ username config
      pass = fmap ("password=" ++) $ password config
      h = fmap ("host=" ++) $ host config
      p = fmap (("port=" ++) . show) (port config)
      result =
        unwords (db : map fromJust (filter isJust [h, p, user, pass]))
  in BS.pack result
