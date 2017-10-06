module Persistence.Utils ( parameterize
                         , advisoryLocked
                         ) where

import Persistence.DBConfig

import Common.Utils (replace)
import Driver.Options
import Persistence.Database

import Control.Monad.IO.Class (MonadIO (..))
import Data.Char
import qualified Data.Text as Text
import Database.Persist hiding (replace)
import Database.Persist.Sql hiding (replace)

parameterize :: String -> String
parameterize =
  dropDashes .
    mergeDashes False .
    map replaceSpecialChars .
    replace "=" "Eq" .
    map toLower
  where
    replaceSpecialChars :: Char -> Char
    replaceSpecialChars c = if ('A' <= c && c <= 'Z') ||
                               ('a' <= c && c <= 'z') ||
                               ('0' <= c && c <= '9')
                            then c
                            else '-'

    mergeDashes :: Bool -> [Char] -> [Char]
    mergeDashes _ [] = []
    mergeDashes previousWasDash (c:cs) =
      if previousWasDash
      then if c == '-'
           then mergeDashes True cs
           else c : mergeDashes False cs
      else if c == '-'
           then c : mergeDashes True cs
           else c : mergeDashes False cs

    dropDashes :: [Char] -> [Char]
    dropDashes = reverse . dropWhile (== '-') . reverse . dropWhile (== '-')

advisoryLocked :: MonadIO m
               => HetcatsOpts -> String -> DBMonad m a -> DBMonad m a
advisoryLocked opts key f =
  case adapter $ databaseConfig opts of
    Just "postgresql" -> do
      advisoryLock key
      f
    _ -> f

advisoryLock :: MonadIO m => String -> DBMonad m [Single (Maybe Text.Text)]
advisoryLock key = do
  let query = Text.pack (
        "SELECT pg_advisory_xact_lock("
        ++ advisoryLockKeyConvert
        ++ ");")
  rawSql query [PersistText $ Text.pack key]

advisoryLockKeyConvert :: String
advisoryLockKeyConvert =
  "(SELECT ('x' || lpad(md5(?),16,'0'))::bit(64)::bigint)"
