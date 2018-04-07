module Persistence.Utils ( firstLibdir
                         , locIdOfDocument
                         , locIdOfOMSWithName
                         , locIdOfOMS
                         , locIdOfSentence
                         , locIdOfSymbol
                         , symbolDetails
                         , locIdOfMapping
                         , slugOfReasoner
                         , slugOfProver
                         , slugOfConsistencyChecker
                         , slugOfTranslation
                         , slugOfLanguageByName
                         , slugOfLogicMapping
                         , slugOfLogicMappingByName
                         , slugOfLogicInclusionByName
                         , slugOfLogicByName
                         , logicNameForDB
                         , logicNameForDBByName
                         , parameterize
                         , advisoryLocked
                         , coerceId
                         ) where

import Persistence.DBConfig

import qualified Persistence.Schema.Enums as Enums
import Persistence.Schema

import Common.Utils (replace, tryToStripPrefix)
import Driver.Options
import Persistence.Database
import Logic.Comorphism as Comorphism
import Logic.Logic as Logic
import Proofs.AbstractState
import Static.DevGraph (DGNodeLab (..))
import Static.DgUtils (showName)

import Control.Monad.IO.Class (MonadIO (..))
import Data.Char
import Data.Maybe
import qualified Data.Text as Text
import qualified Database.Esqueleto.Internal.Language as EIL
import qualified Database.Esqueleto.Internal.Sql as EIS
import Database.Persist hiding (replace)
import Database.Persist.Sql hiding (replace)

firstLibdir :: HetcatsOpts -> String
firstLibdir opts =
  let libdir' = head $ libdirs opts
      libdir'' = if head libdir' == '/' then "file://" ++ libdir' else libdir'
  in  if last libdir'' == '/' then libdir'' else libdir'' ++ "/"

locIdOfDocument :: HetcatsOpts -> Maybe String -> String -> String
locIdOfDocument opts locationM displayName =
  let fullLocation =
        if fmap head locationM == Just '/'
        then fmap ("file://" ++) locationM
        else locationM
      base = fromMaybe displayName fullLocation
  in  if null $ libdirs opts
      then base
      else tryToStripPrefix (firstLibdir opts) base

locIdOfOMSWithName :: Entity LocIdBase -> String -> String
locIdOfOMSWithName (Entity _ documentLocIdBaseValue) nodeName =
  case locIdBaseKind documentLocIdBaseValue of
    Enums.NativeDocument -> nodeName
    _ -> locIdBaseLocId documentLocIdBaseValue
         ++ "//oms/" ++ nodeName

locIdOfOMS :: Entity LocIdBase -> DGNodeLab -> String
locIdOfOMS documentEntity nodeLabel =
  locIdOfOMSWithName documentEntity $ showName $ dgn_name nodeLabel

locIdOfSentence :: Entity LocIdBase -> String -> String
locIdOfSentence (Entity _ omsLocIdBaseValue) name =
  locIdBaseLocId omsLocIdBaseValue ++ "/sentences/" ++ name

symbolDetails :: Logic.Logic lid sublogics
                   basic_spec sentence symb_items symb_map_items
                   sign morphism symbol raw_symbol proof_tree
              => Entity LocIdBase
              -> lid
              -> symbol
              -> (String, String, String, String)
symbolDetails omsEntity lid symbol =
  let name = show $ sym_name lid symbol
      fullName = fullSymName lid symbol
      symbolKind' = symKind lid symbol
      symbolKind = if null symbolKind' then "symbol" else symbolKind'
  in  (locIdOfSymbol omsEntity symbolKind name, name, fullName, symbolKind)

locIdOfSymbol :: Entity LocIdBase -> String -> String -> String
locIdOfSymbol (Entity _ omsLocIdBaseValue) symbolKind' name =
  let symbolKind = if null symbolKind' then "symbol" else symbolKind'
  in  locIdBaseLocId omsLocIdBaseValue ++ "/symbols/" ++ symbolKind ++ "/" ++ name

locIdOfMapping :: Entity LocIdBase -> String -> String
locIdOfMapping (Entity _ documentLocIdBaseValue) displayName =
  locIdBaseLocId documentLocIdBaseValue ++ "//mappings/" ++ displayName

slugOfReasoner :: ProverOrConsChecker -> String
slugOfReasoner proverOrConsChecker =
  case proverOrConsChecker of
    Prover gProver -> slugOfProver gProver
    ConsChecker gConsChecker -> slugOfConsistencyChecker gConsChecker

slugOfProver :: G_prover -> String
slugOfProver = parameterize . getProverName

slugOfConsistencyChecker :: G_cons_checker -> String
slugOfConsistencyChecker = parameterize . getCcName

slugOfTranslation :: AnyComorphism -> String
slugOfTranslation (Comorphism.Comorphism cid) =
  parameterize $ language_name cid

slugOfLanguageByName :: String -> String
slugOfLanguageByName = parameterize

slugOfLogicMapping :: AnyComorphism -> String
slugOfLogicMapping (Comorphism.Comorphism cid) =
  slugOfLogicMappingByName $ language_name cid

slugOfLogicMappingByName :: String -> String
slugOfLogicMappingByName = parameterize

slugOfLogicInclusionByName :: String -> String
slugOfLogicInclusionByName =
  parameterize .
  replace "->" "-Arrow-" .
  replace "_" "-Sub-" .
  replace "." "-Dot-"

slugOfLogicByName :: String -> String
slugOfLogicByName = parameterize

logicNameForDB :: Logic.Logic lid sublogics basic_spec sentence symb_items
                    symb_map_items sign morphism symbol raw_symbol proof_tree
               => lid -> sublogics -> String
logicNameForDB lid sublogic =
  logicNameForDBByName (language_name lid) $ sublogicName sublogic

logicNameForDBByName :: String -> String -> String
logicNameForDBByName languageName_ logicName_ =
  if null logicName_ then languageName_ else logicName_


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
--         on (coerceId (symbols ^. SymbolId) ==. loc_id_bases ^. LocIdBaseId)
--         return symbols
coerceId :: EIS.SqlExpr (EIL.Value a) -> EIS.SqlExpr (EIL.Value b)
coerceId = EIS.veryUnsafeCoerceSqlExprValue
