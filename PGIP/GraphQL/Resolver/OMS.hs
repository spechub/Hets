module PGIP.GraphQL.Resolver.OMS (resolve) where

import PGIP.GraphQL.Resolver.ToResult

import PGIP.GraphQL.Result as GraphQLResult
import PGIP.GraphQL.Result.Mapping as GraphQLResultMapping
import PGIP.GraphQL.Result.PremiseSelection as GraphQLResultPremiseSelection
import PGIP.GraphQL.Result.ReasonerConfiguration as GraphQLResultReasonerConfiguration
import PGIP.GraphQL.Result.ReasoningAttempt as GraphQLResultReasoningAttempt
import PGIP.GraphQL.Result.Sentence as GraphQLResultSentence
import PGIP.GraphQL.Result.StringReference (StringReference (..))
import PGIP.GraphQL.Result.Symbol as GraphQLResultSymbol

import PGIP.Shared

import Driver.Options
import Persistence.Database
import Persistence.Schema as DatabaseSchema
import Persistence.Utils

import Database.Esqueleto

import Control.Monad.IO.Class (MonadIO (..))

resolve :: HetcatsOpts -> Cache -> String -> IO (Maybe GraphQLResult.Result)
resolve opts sessionReference locIdVar =
  onDatabase (databaseConfig opts) $ resolveDB locIdVar

resolveDB :: MonadIO m => String -> DBMonad m (Maybe GraphQLResult.Result)
resolveDB locIdVar = do
  omsL <-
    select $ from $ \(oms `InnerJoin` loc_id_bases
                          `InnerJoin` conservativity_statuses
                          `LeftOuterJoin` file_ranges
                          `LeftOuterJoin` loc_id_basesFreeNormalForm
                          `LeftOuterJoin` signature_morphismsFreeNormalForm
                          `InnerJoin` languages
                          `InnerJoin` logics
                          `LeftOuterJoin` loc_id_basesNormalForm
                          `LeftOuterJoin` signature_morphismsNormalForm) -> do
      on (signature_morphismsNormalForm ?. SignatureMorphismId ==. oms ^. OMSNormalFormSignatureMorphismId)
      on (loc_id_basesNormalForm ?. LocIdBaseId ==. coerceId (oms ^. OMSNormalFormId))
      on (logics ^. LogicId ==. oms ^. OMSLogicId)
      on (languages ^. LanguageId ==. oms ^. OMSLanguageId)
      on (signature_morphismsFreeNormalForm ?. SignatureMorphismId ==. oms ^. OMSFreeNormalFormSignatureMorphismId)
      on (loc_id_basesFreeNormalForm ?. LocIdBaseId ==. coerceId (oms ^. OMSFreeNormalFormId))
      on (file_ranges ?. FileRangeId ==. oms ^. OMSNameFileRangeId)
      on (conservativity_statuses ^. ConservativityStatusId ==. oms ^. OMSConservativityStatusId)
      on (loc_id_bases ^. LocIdBaseId ==. coerceId (oms ^. OMSId))
      where_ (loc_id_bases ^. LocIdBaseLocId ==. val locIdVar)
      return (oms, loc_id_bases, conservativity_statuses, file_ranges,
              loc_id_basesFreeNormalForm, signature_morphismsFreeNormalForm,
              languages, logics,
              loc_id_basesNormalForm, signature_morphismsNormalForm)
  case omsL of
    [] -> return Nothing
    (omsEntity, locIdBaseOMS@(Entity omsKey _ ), conservativityStatusEntity, fileRangeM,
     freeNormalFormLocIdBaseM, freeNormalFormSignatureMorphismM,
     languageEntity, logicEntity,
     normalFormLocIdBaseM, normalFormSignatureMorphismM) : _ -> do
       consistencyCheckAttemptResults <- resolveConsistencyChecks omsKey
       mappingSourceResults <- resolveMappings omsKey MappingSourceId
       mappingTargetResults <- resolveMappings omsKey MappingTargetId
       sentenceResults <- resolveSentences omsKey
       serializationResult <- case oMSSerializationId $ entityVal omsEntity of
         Nothing -> return Nothing
         Just serializationKey -> resolveSerialization serializationKey
       return $ Just $ GraphQLResult.OMSResult $
         omsToResult omsEntity locIdBaseOMS conservativityStatusEntity
           fileRangeM freeNormalFormLocIdBaseM freeNormalFormSignatureMorphismM
           languageEntity logicEntity
           normalFormLocIdBaseM normalFormSignatureMorphismM
           consistencyCheckAttemptResults mappingSourceResults mappingTargetResults
           sentenceResults serializationResult

resolveConsistencyChecks :: MonadIO m
                         => LocIdBaseId -- of the OMS
                         -> DBMonad m [GraphQLResultReasoningAttempt.ReasoningAttempt]
resolveConsistencyChecks omsKey = do
  consistencyCheckAttemptL <-
    select $ from $ \(reasoning_attempts `InnerJoin` consistency_check_attempts
                                         `InnerJoin` reasoner_configurations
                                         `LeftOuterJoin` reasoners) -> do
      on (reasoners ?. ReasonerId ==. reasoning_attempts ^. ReasoningAttemptUsedReasonerId)
      on (reasoner_configurations ^. ReasonerConfigurationId ==. reasoning_attempts ^. ReasoningAttemptReasonerConfigurationId)
      on (coerceId (consistency_check_attempts ^. ConsistencyCheckAttemptId) ==. reasoning_attempts ^. ReasoningAttemptId)
      where_ (consistency_check_attempts ^. ConsistencyCheckAttemptOmsId ==. just (val omsKey))
      return (reasoning_attempts, reasoners, reasoner_configurations)
  mapM resolveReasoningAttempt consistencyCheckAttemptL

resolveMappings :: MonadIO m
                => LocIdBaseId
                -> EntityField DatabaseSchema.Mapping LocIdBaseId
                -> DBMonad m [GraphQLResultMapping.Mapping]
resolveMappings omsKey column = do
  mappingData <-
    select $ from $ \(mappingsSql `InnerJoin` loc_id_bases
                                  `InnerJoin` signature_morphisms
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
      on (mappingsSql ^. MappingSignatureMorphismId ==. signature_morphisms ^. SignatureMorphismId)
      on (loc_id_bases ^. LocIdBaseId ==. coerceId (mappingsSql ^. MappingId))
      where_ (mappingsSql ^. column ==. val omsKey)
      return (mappingsSql, loc_id_bases, signature_morphisms, conservativity_statuses, loc_id_basesSource, loc_id_basesTarget, loc_id_basesOMS, languages)
  return $
    map (\ (mapping, locIdBase, signatureMorphismEntity, conservativityStatusM, locIdBaseSource, locIdBaseTarget, freenesParameterOMSLocIdM, freenessParameterLanguageM) ->
          mappingToResult mapping locIdBase signatureMorphismEntity
            conservativityStatusM locIdBaseSource locIdBaseTarget
            freenesParameterOMSLocIdM freenessParameterLanguageM
        ) mappingData

getReasonerOutput :: MonadIO m
                  => ReasoningAttemptId
                  -> DBMonad m (Maybe (Entity DatabaseSchema.ReasonerOutput))
getReasonerOutput reasoningAttemptKey = do
  reasonerOutputL <- select $ from $ \ reasoner_outputs -> do
    where_ (reasoner_outputs ^. ReasonerOutputReasoningAttemptId ==. val reasoningAttemptKey)
    return reasoner_outputs
  return $ case reasonerOutputL of
    [] -> Nothing
    reasonerOutputEntity : _ -> Just reasonerOutputEntity

resolveReasoningAttempt :: MonadIO m
                        => ( Entity DatabaseSchema.ReasoningAttempt
                           , Maybe (Entity DatabaseSchema.Reasoner)
                           , Entity DatabaseSchema.ReasonerConfiguration
                           )
                        -> DBMonad m GraphQLResultReasoningAttempt.ReasoningAttempt
resolveReasoningAttempt (reasoningAttemptEntity, reasonerEntityM, reasonerConfigurationEntity) = do
  reasonerOutputEntityM <- getReasonerOutput $ entityKey reasoningAttemptEntity
  reasonerConfigurationResult <- resolveReasonerConfiguration reasonerConfigurationEntity
  return $ reasoningAttemptToResult reasoningAttemptEntity reasonerOutputEntityM reasonerEntityM reasonerConfigurationResult

resolveSentences :: MonadIO m
                 => LocIdBaseId -> DBMonad m [GraphQLResultSentence.Sentence]
resolveSentences omsKey = do
  sentenceL <-
    select $ from $ \(sentencesSql `InnerJoin` loc_id_bases
                                `LeftOuterJoin` file_ranges
                                `LeftOuterJoin` conjectures) -> do
      on (coerceId (conjectures ?. ConjectureId) ==. loc_id_bases ^. LocIdBaseId)
      on (file_ranges ?. FileRangeId ==. sentencesSql ^. SentenceFileRangeId)
      on (loc_id_bases ^. LocIdBaseId ==. coerceId (sentencesSql ^. SentenceId))
      where_ (sentencesSql ^. SentenceOmsId ==. val omsKey)
      return (sentencesSql, loc_id_bases, file_ranges, conjectures)
  mapM (\ (sentenceEntity, locIdBaseEntity, fileRangeM, conjectureM) -> do
          symbolResults <- resolveSymbols $ entityKey sentenceEntity
          case conjectureM of
            Nothing -> return $ axiomToResult sentenceEntity locIdBaseEntity fileRangeM symbolResults
            Just conjectureEntity ->
              resolveConjecture sentenceEntity locIdBaseEntity fileRangeM conjectureEntity symbolResults
       ) sentenceL

resolveConjecture :: MonadIO m
                  => Entity DatabaseSchema.Sentence
                  -> Entity DatabaseSchema.LocIdBase
                  -> Maybe (Entity DatabaseSchema.FileRange)
                  -> Entity DatabaseSchema.Conjecture
                  -> [GraphQLResultSymbol.Symbol]
                  -> DBMonad m GraphQLResultSentence.Sentence
resolveConjecture sentenceEntity locIdBaseEntity fileRangeM conjectureEntity symbolResults = do
  proofAttemptResults <- resolveProofAttempts $ entityKey locIdBaseEntity
  return $ conjectureToResult sentenceEntity locIdBaseEntity fileRangeM conjectureEntity symbolResults proofAttemptResults

resolveProofAttempts :: MonadIO m
                     => LocIdBaseId
                     -> DBMonad m [GraphQLResultReasoningAttempt.ReasoningAttempt]
resolveProofAttempts conjectureKey = do
  proofAttemptL <-
    select $ from $ \(reasoning_attempts `InnerJoin` proof_attempts
                                         `InnerJoin` reasoner_configurations
                                         `LeftOuterJoin` reasoners) -> do
      on (reasoners ?. ReasonerId ==. reasoning_attempts ^. ReasoningAttemptUsedReasonerId)
      on (reasoner_configurations ^. ReasonerConfigurationId ==. reasoning_attempts ^. ReasoningAttemptReasonerConfigurationId)
      on (coerceId (proof_attempts ^. ProofAttemptId) ==. reasoning_attempts ^. ReasoningAttemptId)
      where_ (proof_attempts ^. ProofAttemptConjectureId ==. just (val conjectureKey))
      return (reasoning_attempts, reasoners, reasoner_configurations)
  mapM resolveReasoningAttempt proofAttemptL

resolveReasonerConfiguration :: MonadIO m
                             => Entity DatabaseSchema.ReasonerConfiguration
                             -> DBMonad m GraphQLResultReasonerConfiguration.ReasonerConfiguration
resolveReasonerConfiguration reasonerConfigurationEntity@(Entity reasonerConfigurationKey reasonerConfigurationValue) = do
  reasonerL <-
    select $ from $ \ reasoners -> do
      where_ (reasoners ?. ReasonerId ==. val (reasonerConfigurationConfiguredReasonerId reasonerConfigurationValue))
      return reasoners
  let reasonerResultM = case reasonerL of
        [] -> Nothing
        reasonerEntity : _ -> reasonerEntity

  premiseSelectionsL <-
    select $ from $ \ premise_selections -> do
      where_ (premise_selections ^. PremiseSelectionReasonerConfigurationId ==. val reasonerConfigurationKey)
      return premise_selections

  premiseSelectionResults <- mapM resolvePremiseSelection premiseSelectionsL
  return $ reasonerConfigurationToResult reasonerConfigurationEntity reasonerResultM premiseSelectionResults

resolvePremiseSelection :: MonadIO m
                        => Entity DatabaseSchema.PremiseSelection
                        -> DBMonad m GraphQLResultPremiseSelection.PremiseSelection
resolvePremiseSelection (Entity premiseSelectionKey _) = do
  premises <-
    select $ from $ \ (loc_id_bases `InnerJoin` premise_selected_sentences
                                    `InnerJoin` premise_selections) -> do
      on (loc_id_bases ^. LocIdBaseId ==. premise_selected_sentences ^. PremiseSelectedSentencePremiseId)
      on (premise_selected_sentences ^. PremiseSelectedSentencePremiseSelectionId ==. premise_selections ^. PremiseSelectionId)
      where_ (premise_selections ^. PremiseSelectionId ==. val premiseSelectionKey)
      return loc_id_bases
  return $ premiseSelectionToResult premises

resolveSerialization :: MonadIO m
                     => SerializationId
                     -> DBMonad m (Maybe StringReference)
resolveSerialization serializationKey = do
  serializationL <-
    select $ from $ \(serializations) -> do
      where_ (serializations ^. SerializationId ==. val serializationKey)
      return serializations
  case serializationL of
    [] -> return Nothing
    Entity _ serializationValue : _ ->
      return $ Just $ StringReference $ serializationSlug serializationValue

resolveSymbols :: MonadIO m
               => SentenceId -> DBMonad m [GraphQLResultSymbol.Symbol]
resolveSymbols sentenceKey = do
  symbolL <-
    select $ from $ \(symbols `InnerJoin` sentences_symbols
                              `InnerJoin` sentencesSql
                              `InnerJoin` loc_id_bases
                              `LeftOuterJoin` file_ranges) -> do
      on (file_ranges ?. FileRangeId ==. symbols ^. SymbolFileRangeId)
      on (loc_id_bases ^. LocIdBaseId ==. coerceId (symbols ^. SymbolId))
      on (coerceId (sentencesSql ^. SentenceId) ==. sentences_symbols ^. SentenceSymbolSentenceId)
      on (sentences_symbols ^. SentenceSymbolSymbolId ==. coerceId (symbols ^. SymbolId))
      where_ (sentences_symbols ^. SentenceSymbolSentenceId ==. val (toSqlKey $ fromSqlKey sentenceKey))
      return (loc_id_bases, symbols, file_ranges)
  return $ map symbolToResultUncurried symbolL
