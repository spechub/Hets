{-# LANGUAGE FlexibleContexts #-}

module PGIP.GraphQL.Resolver.SignatureMorphism (resolve) where

import PGIP.GraphQL.Resolver.Utils

import PGIP.GraphQL.Result as GraphQLResult
import PGIP.GraphQL.Result.ConservativityStatus as GraphQLResultConservativityStatus
import PGIP.GraphQL.Result.IdReference (IdReference (..))
import PGIP.GraphQL.Result.LanguageMapping as GraphQLResultLanguageMapping
import PGIP.GraphQL.Result.LocIdReference (LocIdReference (..))
import PGIP.GraphQL.Result.LogicMapping as GraphQLResultLogicMapping
import PGIP.GraphQL.Result.Mapping as GraphQLResultMapping
import PGIP.GraphQL.Result.SignatureMorphism as GraphQLResultSignatureMorphism
import PGIP.GraphQL.Result.StringReference (StringReference (..))
import PGIP.GraphQL.Result.SymbolMapping as GraphQLResultSymbolMapping

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
  signatureMorphismL <-
    select $ from $ \(signature_morphisms `InnerJoin` signaturesSource `InnerJoin` signaturesTarget) -> do
      on (signaturesTarget ^. SignatureId ==. signature_morphisms ^. SignatureMorphismTargetId)
      on (signaturesSource ^. SignatureId ==. signature_morphisms ^. SignatureMorphismSourceId)
      where_ (signature_morphisms ^. SignatureMorphismId ==. val (toSqlKey $ fromIntegral idVar))
      return (signature_morphisms, signaturesSource, signaturesTarget)
  case signatureMorphismL of
    [] -> return Nothing
    (Entity signatureMorphismKey _, signatureSource, signatureTarget) : _ -> do
      logicMappingResult <- getLogicMappingResult signatureMorphismKey
      mappingsResults <- getMappingsResults signatureMorphismKey
      symbolMappingResults <- getSymbolMappingResults signatureMorphismKey
      return $ Just $ GraphQLResult.SignatureMorphismResult
        GraphQLResultSignatureMorphism.SignatureMorphism
          { GraphQLResultSignatureMorphism.id = fromIntegral $ fromSqlKey signatureMorphismKey
          , GraphQLResultSignatureMorphism.logicMapping = logicMappingResult
          , GraphQLResultSignatureMorphism.mappings = mappingsResults
          , GraphQLResultSignatureMorphism.source = IdReference $ fromIntegral $ fromSqlKey $ entityKey signatureSource
          , GraphQLResultSignatureMorphism.symbolMappings = symbolMappingResults
          , GraphQLResultSignatureMorphism.target = IdReference $ fromIntegral $ fromSqlKey $ entityKey signatureTarget
          }

getLogicMappingResult :: MonadIO m
                      => SignatureMorphismId
                      -> DBMonad m GraphQLResultLogicMapping.LogicMapping
getLogicMappingResult signatureMorphismKey = do
  (Entity logicMappingKey logicMappingValue, logicSource, logicTarget) : _ <-
    select $ from $ \(signature_morphisms `InnerJoin` logic_mappings `InnerJoin` logicsSource `InnerJoin` logicsTarget) -> do
      on (logic_mappings ^. LogicMappingTargetId ==. logicsTarget ^. LogicId)
      on (logic_mappings ^. LogicMappingSourceId ==. logicsSource ^. LogicId)
      on (signature_morphisms ^. SignatureMorphismLogicMappingId ==. logic_mappings ^. LogicMappingId)
      where_ (signature_morphisms ^. SignatureMorphismId ==. val signatureMorphismKey)
      return (logic_mappings, logicsSource, logicsTarget)
  languageMappingResult <- getLanguageMapping logicMappingKey
  return GraphQLResultLogicMapping.LogicMapping
    { GraphQLResultLogicMapping.id = DatabaseSchema.logicMappingSlug logicMappingValue
    , GraphQLResultLogicMapping.languageMapping = languageMappingResult
    , GraphQLResultLogicMapping.source = StringReference $ DatabaseSchema.logicSlug $ entityVal logicSource
    , GraphQLResultLogicMapping.target = StringReference $ DatabaseSchema.logicSlug $ entityVal logicTarget
    }

getMappingsResults :: MonadIO m
                   => SignatureMorphismId
                   -> DBMonad m [GraphQLResultMapping.Mapping]
getMappingsResults signatureMorphismKey = do
  mappingData <-
    select $ from $ \(signature_morphisms `InnerJoin` mappingsSql
                                          `InnerJoin` loc_id_bases
                                          `LeftOuterJoin` conservativity_statuses
                                          `InnerJoin` loc_id_basesSource
                                          `InnerJoin` loc_id_basesTarget
                                          `LeftOuterJoin` loc_id_basesOMS
                                          `LeftOuterJoin` languages) -> do
      on (languages ?. LanguageId ==. mappingsSql ^. MappingFreenessParameterLanguageId)
      on (loc_id_basesOMS ?. LocIdBaseId ==. mappingsSql ^. MappingFreenessParameterOMSId)
      on (loc_id_basesTarget ^. LocIdBaseId ==. mappingsSql ^. MappingTargetId)
      on (loc_id_basesSource ^. LocIdBaseId ==. mappingsSql ^. MappingSourceId)
      on (conservativity_statuses ?. ConservativityStatusId ==. mappingsSql ^. MappingConservativityStatusId)
      on (loc_id_bases ^. LocIdBaseId ==. coerceLocIdBaseId (mappingsSql ^. MappingId))
      on (mappingsSql ^. MappingSignatureMorphismId ==. signature_morphisms ^. SignatureMorphismId)
      where_ (signature_morphisms ^. SignatureMorphismId ==. val signatureMorphismKey)
      return (mappingsSql, loc_id_bases, conservativity_statuses, loc_id_basesSource, loc_id_basesTarget, loc_id_basesOMS, languages)
  return $
    map (\ (Entity _ mappingValue, locIdBase, conservativityStatusM, locIdBaseSource, locIdBaseTarget, freenesParameterOMSLocIdM, freenessParameterLanguageM) ->
          let conservativityStatusResult = fmap (\ (Entity _ conservativityStatusValue) ->
                GraphQLResultConservativityStatus.ConservativityStatus
                  { GraphQLResultConservativityStatus.required = conservativityStatusRequired conservativityStatusValue
                  , GraphQLResultConservativityStatus.proved = conservativityStatusProved conservativityStatusValue
                  }) conservativityStatusM
              freenessParameterLanguageResult = fmap languageEntityToLanguageResult freenessParameterLanguageM
          in  GraphQLResultMapping.Mapping
                { GraphQLResultMapping.conservativityStatus = conservativityStatusResult
                , GraphQLResultMapping.displayName = mappingDisplayName mappingValue
                , GraphQLResultMapping.freenessParameterOMS = fmap (LocIdReference . locIdBaseLocId . entityVal) freenesParameterOMSLocIdM
                , GraphQLResultMapping.freenessParameterLanguage = freenessParameterLanguageResult
                , GraphQLResultMapping.locId = locIdBaseLocId $ entityVal locIdBase
                , GraphQLResultMapping.name = mappingName mappingValue
                , GraphQLResultMapping.origin = show $ mappingOrigin mappingValue
                , GraphQLResultMapping.pending = mappingPending mappingValue
                , GraphQLResultMapping.signatureMorphism = IdReference $ fromIntegral $ fromSqlKey signatureMorphismKey
                , GraphQLResultMapping.source = LocIdReference $ locIdBaseLocId $ entityVal locIdBaseSource
                , GraphQLResultMapping.target = LocIdReference $ locIdBaseLocId $ entityVal locIdBaseTarget
                , GraphQLResultMapping.mappingType = show $ DatabaseSchema.mappingType mappingValue
                }
        ) mappingData

getSymbolMappingResults :: MonadIO m
                        => SignatureMorphismId
                        -> DBMonad m [GraphQLResultSymbolMapping.SymbolMapping]
getSymbolMappingResults signatureMorphismKey = do
  symbolData <-
    select $ from $ \(signature_morphisms `InnerJoin` symbol_mappings
                                          `InnerJoin` symbolsSource
                                          `InnerJoin` symbolsTarget
                                          `InnerJoin` symbolLoc_id_basesSource
                                          `InnerJoin` symbolLoc_id_basesTarget
                                          `LeftOuterJoin` file_rangesSource
                                          `LeftOuterJoin` file_rangesTarget) -> do
      on (file_rangesTarget ?. FileRangeId ==. symbolsTarget ^. SymbolFileRangeId)
      on (file_rangesSource ?. FileRangeId ==. symbolsSource ^. SymbolFileRangeId)
      on (symbolLoc_id_basesTarget ^. LocIdBaseId ==. coerceLocIdBaseId (symbolsTarget ^. SymbolId))
      on (symbolLoc_id_basesSource ^. LocIdBaseId ==. coerceLocIdBaseId (symbolsSource ^. SymbolId))
      on (coerceLocIdBaseId (symbolsTarget ^. SymbolId) ==. symbol_mappings ^. SymbolMappingTargetId)
      on (coerceLocIdBaseId (symbolsSource ^. SymbolId) ==. symbol_mappings ^. SymbolMappingSourceId)
      on (signature_morphisms ^. SignatureMorphismId ==. symbol_mappings ^. SymbolMappingSignatureMorphismId)
      where_ (signature_morphisms ^. SignatureMorphismId ==. val signatureMorphismKey)
      return ( (symbolLoc_id_basesSource, symbolsSource, file_rangesSource)
             , (symbolLoc_id_basesTarget, symbolsTarget, file_rangesTarget)
             )
  return $
    map (\ (sourceSymbolData, targetSymbolData) ->
           GraphQLResultSymbolMapping.SymbolMapping
             { GraphQLResultSymbolMapping.source = symbolEntityToSymbolResult sourceSymbolData
             , GraphQLResultSymbolMapping.target = symbolEntityToSymbolResult targetSymbolData
             }
        ) symbolData

getLanguageMapping :: MonadIO m
                   => LogicMappingId
                   -> DBMonad m GraphQLResultLanguageMapping.LanguageMapping
getLanguageMapping logicMappingKey = do
  (languageMappingEntity, languageSource, languageTarget) : _ <-
    select $ from $ \(logic_mappings `InnerJoin` language_mappings `InnerJoin` languagesSource `InnerJoin` languagesTarget) -> do
      on (language_mappings ^. LanguageMappingTargetId ==. languagesTarget ^. LanguageId)
      on (language_mappings ^. LanguageMappingSourceId ==. languagesSource ^. LanguageId)
      on (logic_mappings ^. LogicMappingLanguageMappingId ==. language_mappings ^. LanguageMappingId)
      where_ (logic_mappings ^. LogicMappingId ==. val logicMappingKey)
      return (language_mappings, languagesSource, languagesTarget)
  return GraphQLResultLanguageMapping.LanguageMapping
    { GraphQLResultLanguageMapping.id = fromIntegral $ fromSqlKey $ entityKey languageMappingEntity
    , GraphQLResultLanguageMapping.source = StringReference $ DatabaseSchema.languageSlug $ entityVal languageSource
    , GraphQLResultLanguageMapping.target = StringReference $ DatabaseSchema.languageSlug $ entityVal languageTarget
    }
