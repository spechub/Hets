module PGIP.GraphQL.Resolver.Signature (resolve) where

import PGIP.GraphQL.Result as GraphQLResult
import PGIP.GraphQL.Result.LocIdReference
import PGIP.GraphQL.Result.Signature as GraphQLResultSignature

import PGIP.Shared

import Driver.Options
import Persistence.Database
import Persistence.Schema as DatabaseSchema

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Database.Persist
import Database.Persist.Sql

import Control.Monad.IO.Class (MonadIO (..))

resolve :: HetcatsOpts -> Cache -> Int -> IO (Maybe GraphQLResult.Result)
resolve opts sessionReference idVar =
  onDatabase (databaseConfig opts) $ resolveDB idVar

resolveDB :: MonadIO m => Int -> DBMonad m (Maybe GraphQLResult.Result)
resolveDB idVar = do
  signatureM <- selectFirst [ SignatureId ==. toSqlKey (fromIntegral idVar) ] []
  case signatureM of
    Nothing -> return Nothing
    Just (Entity signatureKey signatureValue) -> do
      omsL <- selectList [OMSSignatureId ==. signatureKey] []
      omsLocIds <- mapM locIdOfOMS omsL
      return $ Just $ SignatureResult $ GraphQLResultSignature.Signature
        (fromIntegral $ fromSqlKey signatureKey)
        (map LocIdReference omsLocIds)
        []
        []
        []

locIdOfOMS :: MonadIO m => Entity OMS -> DBMonad m String
locIdOfOMS (Entity omsKey _) = do
  locIdBaseM <- selectFirst [LocIdBaseId ==. toSqlKey (fromSqlKey omsKey)] []
  return $ locIdBaseLocId $ entityVal $ fromJust locIdBaseM
