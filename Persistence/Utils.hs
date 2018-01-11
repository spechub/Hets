module Persistence.Utils ( parameterize
                         , advisoryLocked
                         , coerceLocIdBaseId
                         ) where

import Persistence.DBConfig

import Common.Utils (replace)
import Driver.Options
import Persistence.Database

import Control.Monad.IO.Class (MonadIO (..))
import Data.Char
import qualified Data.Text as Text
import qualified Database.Esqueleto.Internal.Language as EIL
import qualified Database.Esqueleto.Internal.Sql as EIS
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

-- This is used for Esqueleto JOIN statements with
-- "ON subclass.id = loc_id_bases.id"
-- Do NOT use this in other contexts.
-- Usage example:
--     selectedSymbols <- select $ from $
--       \(loc_id_bases `InnerJoin` symbols) -> do
--         on (coerceLocIdBaseId (symbols ^. SymbolId) ==. loc_id_bases ^. LocIdBaseId)
--         return symbols
coerceLocIdBaseId :: EIS.SqlExpr (EIL.Value a) -> EIS.SqlExpr (EIL.Value b)
coerceLocIdBaseId = EIS.veryUnsafeCoerceSqlExprValue
