{-# LANGUAGE FlexibleContexts #-}

module PGIP.GraphQL.Resolver.Signature (resolve) where

import PGIP.GraphQL.Result as GraphQLResult
import PGIP.GraphQL.Result.IdReference (IdReference (..))
import PGIP.GraphQL.Result.LocIdReference (LocIdReference (..))
import PGIP.GraphQL.Result.FileRange as GraphQLResultFileRange
import PGIP.GraphQL.Result.Signature as GraphQLResultSignature
import PGIP.GraphQL.Result.Symbol as GraphQLResultSymbol

import PGIP.Shared

import Driver.Options
import Persistence.Database
import Persistence.Utils
import Persistence.Schema as DatabaseSchema

import qualified Data.Text as Text
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
    Entity signatureKey _ : _ -> do
      omsL <- select $ from $ \(omsSql `InnerJoin` loc_id_bases) -> do
        on (coerceLocIdBaseId (omsSql ^. OMSId) ==. loc_id_bases ^. LocIdBaseId)
        where_ (omsSql ^. OMSSignatureId ==. val signatureKey)
        return loc_id_bases
      let omsLocIds = map (locIdBaseLocId . entityVal) omsL

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
      symbolResults <- mapM toSymbolResult symbolsWithFileRanges

      return $ Just $ SignatureResult $ GraphQLResultSignature.Signature
        (fromIntegral $ fromSqlKey signatureKey)
        (map LocIdReference omsLocIds)
        (map (IdReference . fromIntegral . fromSqlKey . entityKey) signatureMorphismsAsSourceL)
        (map (IdReference . fromIntegral . fromSqlKey . entityKey) signatureMorphismsAsTargetL)
        symbolResults

toSymbolResult :: MonadIO m
               => ( Entity DatabaseSchema.LocIdBase
                  , Entity DatabaseSchema.Symbol
                  , Maybe (Entity DatabaseSchema.FileRange)
                  )
               -> DBMonad m GraphQLResultSymbol.Symbol
toSymbolResult (Entity _ locIdBaseValue, Entity _ symbolValue, fileRangeM) = do
  let fileRangeResult =
        fmap (\(Entity _ fileRangeValue) -> GraphQLResultFileRange.FileRange
               { GraphQLResultFileRange.startLine = fileRangeStartLine fileRangeValue
               , GraphQLResultFileRange.startColumn = fileRangeStartColumn fileRangeValue
               , GraphQLResultFileRange.endLine = fileRangeEndLine fileRangeValue
               , GraphQLResultFileRange.endColumn = fileRangeEndColumn fileRangeValue
               , GraphQLResultFileRange.path = fileRangePath fileRangeValue
               }) fileRangeM
  return GraphQLResultSymbol.Symbol
    { GraphQLResultSymbol.__typename = "Symbol"
    , GraphQLResultSymbol.fileRange = fileRangeResult
    , GraphQLResultSymbol.fullName = Text.unpack $ symbolFullName symbolValue
    , GraphQLResultSymbol.kind = symbolSymbolKind symbolValue
    , GraphQLResultSymbol.locId = locIdBaseLocId locIdBaseValue
    , GraphQLResultSymbol.name = symbolName symbolValue
    }
