{-# LANGUAGE CPP                        #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE ScopedTypeVariables        #-}

#ifdef MYSQL
module Persistence.MySQL (connection) where

import Persistence.DBConfig

import Control.Monad.IO.Class
import Control.Monad.Trans.Control
import Control.Monad.Logger
import Data.Maybe
import Data.Pool (Pool)
import Database.Persist.MySQL

connection :: ( BaseBackend backend ~ SqlBackend
              , IsPersistBackend backend
              , MonadIO m
              , MonadBaseControl IO m
              , MonadLogger m
              )
           => DBConfig -> Int -> (Pool backend -> m a) -> m a
connection dbConfig defaultPoolSize =
  withMySQLPool (connectionInfo dbConfig) $
    fromMaybe defaultPoolSize $ pool dbConfig

connectionInfo :: DBConfig -> ConnectInfo
connectionInfo config =
  let hostArg = fromMaybe (connectHost defaultConnectInfo) $ host config
      portArg = case port config of
        Nothing -> connectPort defaultConnectInfo
        Just p -> fromIntegral p
      userArg = fromMaybe (connectUser defaultConnectInfo) $ username config
      passArg = fromMaybe (connectPassword defaultConnectInfo) $ password config
  in  defaultConnectInfo { connectHost = hostArg
                         , connectPort = portArg
                         , connectUser = userArg
                         , connectPassword = passArg
                         , connectDatabase = database config
                         }
#endif
