{-# LANGUAGE FlexibleContexts #-}

module PGIP.GraphQL.Resolver.Signature (resolve) where

import PGIP.GraphQL.Resolver.ToResult

import PGIP.GraphQL.Result as GraphQLResult

import PGIP.Shared

import Driver.Options
import Persistence.Database
import Persistence.Utils
import Persistence.Schema as DatabaseSchema

import Database.Esqueleto

import Control.Monad.IO.Class (MonadIO (..))

resolve :: HetcatsOpts -> Cache -> Int -> IO (Maybe GraphQLResult.Result)
resolve opts sessionReference idVar =
  onDatabase (databaseConfig opts) $ resolveDB idVar

resolveDB :: MonadIO m => Int -> DBMonad m (Maybe GraphQLResult.Result)
resolveDB idVar = do
  signatureL <- select $ from $ \signatures -> do
    where_ (signatures ^. SignatureId ==. val (toSqlKey $ fromIntegral idVar))
    return signatures
  case signatureL of
    [] -> return Nothing
    signatureEntity@(Entity signatureKey _) : _ -> do
      omsL <- select $ from $ \(omsSql `InnerJoin` loc_id_bases) -> do
        on (coerceLocIdBaseId (omsSql ^. OMSId) ==. loc_id_bases ^. LocIdBaseId)
        where_ (omsSql ^. OMSSignatureId ==. val signatureKey)
        return loc_id_bases

      signatureMorphismsAsSourceL <- select $ from $ \signature_morphisms -> do
        where_ (signature_morphisms ^. SignatureMorphismSourceId ==. val signatureKey)
        return signature_morphisms

      signatureMorphismsAsTargetL <- select $ from $ \signature_morphisms -> do
        where_ (signature_morphisms ^. SignatureMorphismTargetId ==. val signatureKey)
        return signature_morphisms

      symbolsWithFileRanges <- select $ from $
        \(signatures `InnerJoin` signature_symbols `InnerJoin` loc_id_bases `InnerJoin` symbolsSql `LeftOuterJoin` file_ranges) -> do
          on (file_ranges ?. FileRangeId ==. symbolsSql ^. SymbolFileRangeId)
          on (coerceLocIdBaseId (symbolsSql ^. SymbolId) ==. loc_id_bases ^. LocIdBaseId)
          on (loc_id_bases ^. LocIdBaseId ==. signature_symbols ^. SignatureSymbolSymbolId)
          on (signature_symbols ^. SignatureSymbolSignatureId ==. signatures ^. SignatureId)
          where_ (signatures ^. SignatureId ==. val signatureKey)
          return (loc_id_bases, symbolsSql, file_ranges)

      return $ Just $ SignatureResult $ signatureToResult signatureEntity omsL signatureMorphismsAsSourceL signatureMorphismsAsTargetL symbolsWithFileRanges
