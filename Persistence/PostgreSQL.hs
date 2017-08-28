module Persistence.PostgreSQL where

import Persistence.DBConfig

import qualified Data.ByteString.Char8 as BS
import Data.List (intercalate)
import Data.Maybe

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
