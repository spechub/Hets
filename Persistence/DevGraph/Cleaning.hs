{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeFamilies               #-}

{- |
Module      :  ./Persistence.DevGraph.hs
Copyright   :  (c) Uni Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  portable
-}

module Persistence.DevGraph.Cleaning (clean) where

import Persistence.Database
import Persistence.Schema

import Control.Monad (when)
import Control.Monad.IO.Class (MonadIO (..))
import Database.Persist
import Database.Persist.Sql
import GHC.Int

clean :: MonadIO m => Entity LocIdBase -> DBMonad m ()
clean (Entity documentKey documentValue) = do
  deleteDocument documentKey
  deleteDiagnoses $ locIdBaseFileVersionId documentValue

deleteDiagnoses :: MonadIO m => FileVersionId -> DBMonad m ()
deleteDiagnoses key = deleteCascadeWhere [DiagnosisFileVersionId ==. key]

deleteDocument :: MonadIO m => LocIdBaseId -> DBMonad m ()
deleteDocument key = do
  deleteDocumentLinks key
  deleteOms key
  deleteWhere [DocumentId ==. toSqlKey (fromSqlKey key)]
  deleteWhere [LocIdBaseId ==. key]

deleteDocumentLinks :: MonadIO m => LocIdBaseId -> DBMonad m ()
deleteDocumentLinks documentKey =
  deleteWhere (   [DocumentLinkSourceId ==. documentKey]
              ||. [DocumentLinkTargetId ==. documentKey]
              )

deleteOms :: MonadIO m => LocIdBaseId -> DBMonad m ()
deleteOms documentKey = do
  omsL <- selectList [OMSDocumentId ==. documentKey] []
  mapM_ (\ (Entity omsKey omsValue) -> do
          maybe (return ()) deleteOms $ oMSNormalFormId omsValue
          maybe (return ()) deleteOms $ oMSFreeNormalFormId omsValue
          deleteMappings $ toSqlKey $ fromSqlKey omsKey
          deleteSentences $ toSqlKey $ fromSqlKey omsKey
          deleteSymbols $ toSqlKey $ fromSqlKey omsKey
          deleteConsistencyCheckAttempts $ toSqlKey $ fromSqlKey omsKey
          deleteWhere [LocIdBaseId ==. toSqlKey (fromSqlKey omsKey)]
          delete omsKey
          deleteSignature $ oMSSignatureId omsValue
        ) omsL

deleteMappings :: MonadIO m => LocIdBaseId -> DBMonad m ()
deleteMappings omsKey = do
  mappings <- selectList (   [MappingSourceId ==. omsKey]
                         ||. [MappingTargetId ==. omsKey]
                         ||. [MappingFreenessParameterOMSId ==. Just omsKey]
                         ) []
  mapM_ (\ (Entity mappingKey _) -> do
          deleteWhere [LocIdBaseId ==. toSqlKey (fromSqlKey mappingKey)]
          delete mappingKey
        ) mappings

deleteSentences :: MonadIO m => LocIdBaseId -> DBMonad m ()
deleteSentences omsKey = do
  sentences <- selectList [SentenceOmsId ==. omsKey] []
  mapM_ (\ (Entity sentenceKey _) -> do
          deleteSentencesSymbols $ toSqlKey $ fromSqlKey sentenceKey
          deletePremiseSelectedSentences $ toSqlKey $ fromSqlKey sentenceKey
          deleteAxiom $ toSqlKey $ fromSqlKey sentenceKey
          deleteConjecture $ toSqlKey $ fromSqlKey sentenceKey
          deleteWhere [LocIdBaseId ==. toSqlKey (fromSqlKey sentenceKey)]
        ) sentences
  deleteWhere [SentenceOmsId ==. omsKey]

deleteSentencesSymbols :: MonadIO m => LocIdBaseId -> DBMonad m ()
deleteSentencesSymbols sentenceKey =
  deleteWhere [SentenceSymbolSentenceId ==. sentenceKey]

deletePremiseSelectedSentences :: MonadIO m => LocIdBaseId -> DBMonad m ()
deletePremiseSelectedSentences sentenceKey =
  deleteWhere [PremiseSelectedSentencePremiseId ==. sentenceKey]

deleteAxiom :: MonadIO m => LocIdBaseId -> DBMonad m ()
deleteAxiom = delete

deleteConjecture :: MonadIO m => LocIdBaseId -> DBMonad m ()
deleteConjecture conjectureKey = do
  deleteProofAttempts conjectureKey
  delete conjectureKey

deleteProofAttempts :: MonadIO m => LocIdBaseId -> DBMonad m ()
deleteProofAttempts conjectureKey = do
  proofAttempts <- selectList [ProofAttemptConjectureId ==. Just conjectureKey] []
  mapM_ (\ (Entity proofAttemptKey _) ->
          deleteReasoningAttempt $ fromSqlKey proofAttemptKey
        ) proofAttempts
  deleteWhere [ProofAttemptConjectureId ==. Just conjectureKey]

deleteReasoningAttempt :: MonadIO m => GHC.Int.Int64 -> DBMonad m ()
deleteReasoningAttempt keyInt = do
  let reasoningAttemptKey = toSqlKey keyInt
  reasoningAttemptValueM <- get reasoningAttemptKey
  deleteGeneratedAxioms reasoningAttemptKey
  deleteReasonerOutputs reasoningAttemptKey
  delete reasoningAttemptKey
  case reasoningAttemptValueM of
    Just reasoningAttemptValue -> deleteReasoningConfiguration $ reasoningAttemptReasonerConfigurationId reasoningAttemptValue
    Nothing -> return ()

deleteGeneratedAxioms :: MonadIO m => ReasoningAttemptId -> DBMonad m ()
deleteGeneratedAxioms reasoningAttemptKey =
  deleteWhere [GeneratedAxiomReasoningAttemptId ==. reasoningAttemptKey]

deleteReasonerOutputs :: MonadIO m => ReasoningAttemptId -> DBMonad m ()
deleteReasonerOutputs reasoningAttemptKey =
  deleteWhere [ReasonerOutputReasoningAttemptId ==. reasoningAttemptKey]

deleteReasoningConfiguration :: MonadIO m
                             => ReasonerConfigurationId -> DBMonad m ()
deleteReasoningConfiguration reasoningConfigurationKey = do
  reasoningAttempts <- selectList [ReasoningAttemptReasonerConfigurationId ==. reasoningConfigurationKey] []
  when (null reasoningAttempts) $ do
    deletePremiseSelections reasoningConfigurationKey
    delete reasoningConfigurationKey

deletePremiseSelections :: MonadIO m => ReasonerConfigurationId -> DBMonad m ()
deletePremiseSelections reasoningConfigurationKey = do
  premiseSelections <- selectList [PremiseSelectionReasonerConfigurationId ==. reasoningConfigurationKey] []
  mapM_ (\ (Entity premiseSelectionKey _) -> do
          deleteManualPremiseSelection $ toSqlKey $ fromSqlKey premiseSelectionKey
          deleteSinePremiseSelection $ toSqlKey $ fromSqlKey premiseSelectionKey
        ) premiseSelections
  deleteWhere [PremiseSelectionReasonerConfigurationId ==. reasoningConfigurationKey]

deleteManualPremiseSelection :: MonadIO m => ManualPremiseSelectionId -> DBMonad m ()
deleteManualPremiseSelection = delete

deleteSinePremiseSelection :: MonadIO m => SinePremiseSelectionId -> DBMonad m ()
deleteSinePremiseSelection sinePremiseSelectionKey = do
  deleteSineSymbolPremiseTriggers sinePremiseSelectionKey
  deleteSineSymbolCommonnesses sinePremiseSelectionKey
  delete sinePremiseSelectionKey

deleteSineSymbolPremiseTriggers :: MonadIO m => SinePremiseSelectionId -> DBMonad m ()
deleteSineSymbolPremiseTriggers sinePremiseSelectionKey =
  deleteWhere [SineSymbolPremiseTriggerSinePremiseSelectionId ==. sinePremiseSelectionKey]

deleteSineSymbolCommonnesses :: MonadIO m => SinePremiseSelectionId -> DBMonad m ()
deleteSineSymbolCommonnesses sinePremiseSelectionKey =
  deleteWhere [SineSymbolCommonnessSinePremiseSelectionId ==. sinePremiseSelectionKey]

deleteSymbols :: MonadIO m => LocIdBaseId -> DBMonad m ()
deleteSymbols omsKey = do
  symbols <- selectList [SymbolOmsId ==. omsKey] []
  mapM_ (\ (Entity symbolKey _) -> do
          deleteSymbolMappings $ toSqlKey $ fromSqlKey symbolKey
          deleteSignatureSymbols $ toSqlKey $ fromSqlKey symbolKey
          deleteWhere [LocIdBaseId ==. toSqlKey (fromSqlKey symbolKey)]
        ) symbols
  deleteWhere [SymbolOmsId ==. omsKey]

deleteSymbolMappings :: MonadIO m => LocIdBaseId -> DBMonad m ()
deleteSymbolMappings symbolKey =
  deleteWhere (   [SymbolMappingSourceId ==. symbolKey]
              ||. [SymbolMappingTargetId ==. symbolKey]
              )

deleteSignatureSymbols :: MonadIO m => LocIdBaseId -> DBMonad m ()
deleteSignatureSymbols symbolKey =
  deleteWhere [SignatureSymbolSymbolId ==. symbolKey]

deleteConsistencyCheckAttempts :: MonadIO m => LocIdBaseId -> DBMonad m ()
deleteConsistencyCheckAttempts omsKey = do
  consistencyCheckAttempts <-
    selectList [ConsistencyCheckAttemptOmsId ==. Just omsKey] []
  mapM_ (\ (Entity consistencyCheckAttemptKey _) ->
          deleteReasoningAttempt $ fromSqlKey consistencyCheckAttemptKey
        ) consistencyCheckAttempts
  deleteWhere [ConsistencyCheckAttemptOmsId ==. Just omsKey]

deleteSignature :: MonadIO m => SignatureId -> DBMonad m ()
deleteSignature signatureKey = do
  oms <- selectList [OMSSignatureId ==. signatureKey] []
  when (null oms) $ do
    deleteSignatureMorphisms signatureKey
    delete signatureKey

deleteSignatureMorphisms :: MonadIO m => SignatureId -> DBMonad m ()
deleteSignatureMorphisms signatureKey =
  deleteWhere (   [SignatureMorphismSourceId ==. signatureKey]
              ||. [SignatureMorphismTargetId ==. signatureKey]
              )
