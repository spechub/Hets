{-# LANGUAGE DeriveGeneric #-}

module Persistence.DBConfig where

import qualified Data.ByteString.Char8 as BS
import Data.Aeson
import qualified Data.Yaml as Yaml
import GHC.Generics
import System.Directory

data ExtDBConfig = ExtDBConfig { development :: Maybe DBConfig
                               , test :: Maybe DBConfig
                               , production :: Maybe DBConfig
                               } deriving (Show, Generic)

data DBConfig = DBConfig { adapter :: Maybe String
                         , database :: String
                         , username :: Maybe String
                         , password :: Maybe String
                         , host :: Maybe String
                         , port :: Maybe Int
                         , template :: Maybe String
                         , encoding :: Maybe String
                         , locale :: Maybe String
                         , pool :: Maybe Int
                         } deriving (Show, Generic)

instance FromJSON ExtDBConfig
instance FromJSON DBConfig

emptyDBConfig :: DBConfig
emptyDBConfig = DBConfig { adapter = Nothing
                         , database = ""
                         , username = Nothing
                         , password = Nothing
                         , host = Nothing
                         , port = Nothing
                         , template = Nothing
                         , encoding = Nothing
                         , locale = Nothing
                         , pool = Nothing
                         }

databaseConfig :: FilePath -> FilePath -> String -> IO DBConfig
databaseConfig dbFile dbConfigFile subconfigKey =
  case (null dbFile, null dbConfigFile) of
     (True, True) -> fail ("No database configuration supplied. "
                           ++ "Please specify either --database-config "
                           ++ "or --database-file.")
     (_, False) -> configFromYaml dbConfigFile
     (False, _) -> return $ sqliteConfig dbFile
  where
    sqliteConfig :: FilePath -> DBConfig
    sqliteConfig filepath = emptyDBConfig { adapter = Just "sqlite"
                                          , database = filepath
                                          }

    configFromYaml :: FilePath -> IO DBConfig
    configFromYaml dbConfigFile = do
      fileExist <- doesFileExist dbConfigFile
      if fileExist
      then do
        content <- BS.readFile dbConfigFile
        case subconfigKey of
          "" -> parseDBConfig content
          _ | subconfigKey `elem` ["production", "development", "test"] ->
            parseExtDBConfig subconfigKey content
          _ -> fail "Persistence.DBConfig: Bad database-subconfig specified."
      else
        fail "Persistence.DBConfig: Database configuration file does not exist."

    parseDBConfig :: BS.ByteString -> IO DBConfig
    parseDBConfig content =
      let parsedContent = Yaml.decode content :: Maybe DBConfig
      in case parsedContent of
        Nothing ->
          fail "Persistence.DBConfig: Could not parse database config file."
        Just dbConfig -> return dbConfig

    parseExtDBConfig :: String -> BS.ByteString -> IO DBConfig
    parseExtDBConfig subconfigKey content =
      let parsedContent = Yaml.decode content :: Maybe ExtDBConfig
      in case parsedContent of
        Nothing ->
          fail "Persistence.DBConfig: Could not parse database config file."
        Just extDbConfig ->
          let field = if subconfigKey == "production" then production
                      else if subconfigKey == "development" then development
                      else test
          in case field extDbConfig of
            Nothing ->
              fail ("Persistence.DBConfig: Could not find subconfig "
                ++ subconfigKey ++ " in database configuration file.")
            Just dbConfig -> return dbConfig
