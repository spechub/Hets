module PGIP.GraphQL.Resolver.DGraph (resolve) where

import PGIP.GraphQL.Resolver.ToResult

import PGIP.GraphQL.Result as GraphQLResult
import PGIP.GraphQL.Result.DGraph as GraphQLResultDGraph
import PGIP.GraphQL.Result.DocumentLink as GraphQLResultDocumentLink
import PGIP.GraphQL.Result.OMSSimple as GraphQLResultOMSSimple

import PGIP.Shared

import Driver.Options
import Persistence.Database
import Persistence.Schema as DatabaseSchema
import Persistence.Schema.Enums as DatabaseSchemaEnums
import Persistence.Utils

import Database.Esqueleto

import Control.Monad.IO.Class (MonadIO (..))

resolve :: HetcatsOpts -> Cache -> String -> IO (Maybe GraphQLResult.Result)
resolve opts sessionReference locIdVar =
  onDatabase (databaseConfig opts) $ resolveDB locIdVar

resolveDB :: MonadIO m => String -> DBMonad m (Maybe GraphQLResult.Result)
resolveDB locIdVar = do
  dgraphL <-
    select $ from $ \(documents `InnerJoin` loc_id_bases) -> do
      on (loc_id_bases ^. LocIdBaseId ==. coerceId (documents ^. DocumentId))
      where_ (loc_id_bases ^. LocIdBaseLocId ==. val locIdVar)
      return (documents, loc_id_bases)
  case dgraphL of
    [] -> return Nothing
    (documentEntity, locIdBaseEntity@(Entity documentKey _)) : _ -> do
      documentLinksSourceResults <- resolveDocumentLinks documentKey DocumentLinkSourceId
      documentLinksTargetResults <- resolveDocumentLinks documentKey DocumentLinkTargetId
      omsResults <- resolveOMS documentKey
      case locIdBaseKind $ entityVal locIdBaseEntity of
        DatabaseSchemaEnums.Library ->
          return $ Just $ GraphQLResult.DGraphResult $ GraphQLResultDGraph.DGLibrary $
            libraryToResult documentEntity locIdBaseEntity documentLinksSourceResults documentLinksTargetResults omsResults
        DatabaseSchemaEnums.NativeDocument -> do
          omsResult <- case omsResults of
            [] -> fail ("No OMS found for document " ++ locIdVar)
            oms : _ -> return oms
          return $ Just $ GraphQLResult.DGraphResult $ GraphQLResultDGraph.DGNativeDocument $
            nativeDocumentToResult documentEntity locIdBaseEntity documentLinksSourceResults documentLinksTargetResults omsResult
        _ -> fail ("Bad kind of document in database at locId " ++ locIdVar)

resolveDocumentLinks :: MonadIO m
                     => LocIdBaseId
                     -> EntityField DatabaseSchema.DocumentLink LocIdBaseId
                     -> DBMonad m [GraphQLResultDocumentLink.DocumentLink]
resolveDocumentLinks documentKey column = do
  documentLinksL <-
    select $ from $ \ (document_links `InnerJoin` loc_id_basesSource
                                      `InnerJoin` loc_id_basesTarget) -> do
      on (document_links ^. DocumentLinkTargetId ==. loc_id_basesTarget ^. LocIdBaseId)
      on (document_links ^. DocumentLinkSourceId ==. loc_id_basesSource ^. LocIdBaseId)
      where_ (document_links ^. column ==. val documentKey)
      return (loc_id_basesSource, loc_id_basesTarget)
  return $ map (uncurry documentLinkToResult) documentLinksL

resolveOMS :: MonadIO m
           => LocIdBaseId
           -> DBMonad m [GraphQLResultOMSSimple.OMSSimple]
resolveOMS documentKey = do
  omsL <-
    select $ from $ \ (oms `InnerJoin` loc_id_basesDocument `InnerJoin` loc_id_bases) -> do
      on (loc_id_bases ^. LocIdBaseId ==. coerceId (oms ^. OMSId))
      on (loc_id_basesDocument ^. LocIdBaseId ==. oms ^. OMSDocumentId)
      where_ (loc_id_basesDocument ^. LocIdBaseId ==. val documentKey)
      return (oms, loc_id_bases)
  return $ map (uncurry omsToResultSimple) omsL
