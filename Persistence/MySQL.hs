module Persistence.MySQL where

import Persistence.DBConfig

import Data.Maybe
import Database.Persist.MySQL

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
