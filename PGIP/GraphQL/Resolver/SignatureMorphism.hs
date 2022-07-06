{-# LANGUAGE FlexibleContexts #-}

module PGIP.GraphQL.Resolver.SignatureMorphism (resolve) where

import PGIP.GraphQL.Resolver.ToResult

import PGIP.GraphQL.Result as GraphQLResult
import PGIP.GraphQL.Result.LanguageMapping as GraphQLResultLanguageMapping
import PGIP.GraphQL.Result.LogicMapping as GraphQLResultLogicMapping
import PGIP.GraphQL.Result.Mapping as GraphQLResultMapping
import PGIP.GraphQL.Result.SymbolMapping as GraphQLResultSymbolMapping

import PGIP.Shared

import Driver.Options
import Persistence.Database
import Persistence.Utils
import Persistence.Schema as DatabaseSchema

import Database.Esqueleto

import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.Fail

resolve :: HetcatsOpts -> Cache -> Int -> IO (Maybe GraphQLResult.Result)
resolve opts sessionReference idVar =
  onDatabase (databaseConfig opts) $ resolveDB idVar

resolveDB :: (MonadIO m, MonadFail m) => Int -> DBMonad m (Maybe GraphQLResult.Result)
resolveDB idVar = do
  signatureMorphismL <-
    select $ from $ \(signature_morphisms `InnerJoin` signaturesSource
                                          `InnerJoin` signaturesTarget) -> do
      on (signaturesTarget ^. SignatureId ==.
            signature_morphisms ^. SignatureMorphismTargetId)
      on (signaturesSource ^. SignatureId ==.
            signature_morphisms ^. SignatureMorphismSourceId)
      where_ (signature_morphisms ^. SignatureMorphismId ==.
                val (toSqlKey $ fromIntegral idVar))
      return (signature_morphisms, signaturesSource, signaturesTarget)
  case signatureMorphismL of
    [] -> return Nothing
    (signatureMorphismEntity@(Entity signatureMorphismKey _),
     signatureSource, signatureTarget) : _ -> do
      logicMappingResult <- getLogicMappingResult signatureMorphismKey
      mappingResults <- getMappingsResults signatureMorphismKey
      symbolMappingResults <- getSymbolMappingResults signatureMorphismKey
      return $ Just $ GraphQLResult.SignatureMorphismResult $
        signatureMorphismToResult signatureMorphismEntity signatureSource
          signatureTarget logicMappingResult mappingResults symbolMappingResults

getLogicMappingResult :: (MonadIO m, MonadFail m)
                      => SignatureMorphismId
                      -> DBMonad m GraphQLResultLogicMapping.LogicMapping
getLogicMappingResult signatureMorphismKey = do
  (logicMappingEntity@(Entity logicMappingKey _), logicSource, logicTarget) : _ <-
    select $ from $ \ (signature_morphisms `InnerJoin` logic_mappings
                                           `InnerJoin` logicsSource
                                           `InnerJoin` logicsTarget) -> do
      on (logic_mappings ^. LogicMappingTargetId ==. logicsTarget ^. LogicId)
      on (logic_mappings ^. LogicMappingSourceId ==. logicsSource ^. LogicId)
      on (signature_morphisms ^. SignatureMorphismLogicMappingId ==.
            logic_mappings ^. LogicMappingId)
      where_ (signature_morphisms ^. SignatureMorphismId ==.
            val signatureMorphismKey)
      return (logic_mappings, logicsSource, logicsTarget)
  languageMappingResult <- getLanguageMapping logicMappingKey
  return $ logicMappingToResult logicMappingEntity logicSource logicTarget
    languageMappingResult

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
      on (languages ?. LanguageId ==.
            mappingsSql ^. MappingFreenessParameterLanguageId)
      on (loc_id_basesOMS ?. LocIdBaseId ==.
            mappingsSql ^. MappingFreenessParameterOMSId)
      on (loc_id_basesTarget ^. LocIdBaseId ==. mappingsSql ^. MappingTargetId)
      on (loc_id_basesSource ^. LocIdBaseId ==. mappingsSql ^. MappingSourceId)
      on (conservativity_statuses ?. ConservativityStatusId ==.
            mappingsSql ^. MappingConservativityStatusId)
      on (loc_id_bases ^. LocIdBaseId ==. coerceId (mappingsSql ^. MappingId))
      on (mappingsSql ^. MappingSignatureMorphismId ==.
            signature_morphisms ^. SignatureMorphismId)
      where_ (signature_morphisms ^. SignatureMorphismId ==.
               val signatureMorphismKey)
      return (mappingsSql, loc_id_bases, signature_morphisms,
              conservativity_statuses, loc_id_basesSource, loc_id_basesTarget,
              loc_id_basesOMS, languages)
  return $
    map (\ (mapping, locIdBase, signatureMorphismEntity, conservativityStatusM,
            locIdBaseSource, locIdBaseTarget, freenesParameterOMSLocIdM,
            freenessParameterLanguageM) ->
          mappingToResult mapping locIdBase signatureMorphismEntity
            conservativityStatusM locIdBaseSource locIdBaseTarget
            freenesParameterOMSLocIdM freenessParameterLanguageM
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
      on (file_rangesTarget ?. FileRangeId ==.
            symbolsTarget ^. SymbolFileRangeId)
      on (file_rangesSource ?. FileRangeId ==.
            symbolsSource ^. SymbolFileRangeId)
      on (symbolLoc_id_basesTarget ^. LocIdBaseId ==.
            coerceId (symbolsTarget ^. SymbolId))
      on (symbolLoc_id_basesSource ^. LocIdBaseId ==.
            coerceId (symbolsSource ^. SymbolId))
      on (coerceId (symbolsTarget ^. SymbolId) ==.
            symbol_mappings ^. SymbolMappingTargetId)
      on (coerceId (symbolsSource ^. SymbolId) ==.
            symbol_mappings ^. SymbolMappingSourceId)
      on (signature_morphisms ^. SignatureMorphismId ==.
            symbol_mappings ^. SymbolMappingSignatureMorphismId)
      where_ (signature_morphisms ^. SignatureMorphismId ==.
                val signatureMorphismKey)
      return ( (symbolLoc_id_basesSource, symbolsSource, file_rangesSource)
             , (symbolLoc_id_basesTarget, symbolsTarget, file_rangesTarget)
             )
  return $ map (uncurry symbolMappingToResult) symbolData

getLanguageMapping :: (MonadIO m, MonadFail m)
                   => LogicMappingId
                   -> DBMonad m GraphQLResultLanguageMapping.LanguageMapping
getLanguageMapping logicMappingKey = do
  (languageMappingEntity, languageSource, languageTarget) : _ <-
    select $ from $ \(logic_mappings `InnerJoin` language_mappings
                                     `InnerJoin` languagesSource
                                     `InnerJoin` languagesTarget) -> do
      on (language_mappings ^. LanguageMappingTargetId ==.
            languagesTarget ^. LanguageId)
      on (language_mappings ^. LanguageMappingSourceId ==.
            languagesSource ^. LanguageId)
      on (logic_mappings ^. LogicMappingLanguageMappingId ==.
            language_mappings ^. LanguageMappingId)
      where_ (logic_mappings ^. LogicMappingId ==. val logicMappingKey)
      return (language_mappings, languagesSource, languagesTarget)
  return $
    languageMappingToResult languageMappingEntity languageSource languageTarget
