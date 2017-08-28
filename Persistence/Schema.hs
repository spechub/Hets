{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE QuasiQuotes                #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}

{- |
Module      :  ./Persistence.DevGraph.hs
Copyright   :  (c) Uni Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  portable
-}

module Persistence.Schema where

import Database.Persist.Sql
import Database.Persist.TH

import Data.Text (Text)

import Persistence.Schema.ConjectureKindType (ConjectureKindType)
import Persistence.Schema.DocumentKindType (DocumentKindType)
import qualified Persistence.Schema.Enums as Enums
import Persistence.Schema.EvaluationStateType (EvaluationStateType)
import Persistence.Schema.MappingOrigin (MappingOrigin)
import Persistence.Schema.MappingType (MappingType)
import Persistence.Schema.OMSOrigin (OMSOrigin)
import Persistence.Schema.ReasoningStatusOnConjectureType (ReasoningStatusOnConjectureType)
import Persistence.Schema.ReasoningStatusOnReasoningAttemptType (ReasoningStatusOnReasoningAttemptType)
import Persistence.Schema.SentenceKindType (SentenceKindType)

share [mkPersist sqlSettings, mkMigrate "migrateAll"] [persistLowerCase|
Hets sql=hets
  key String
  Primary key
  value String
  deriving Show

Language sql=languages
  slug String
  UniqueLanguageSlug slug
  name String
  description String
  standardizationStatus String
  definedBy String
  deriving Show

Logic sql=logics
  languageId LanguageId
  slug String
  UniqueLanguageIdLogicSlug languageId slug
  name String
  deriving Show

LanguageMapping sql=language_mappings
  sourceId LanguageId
  targetId LanguageId
  deriving Show

LogicMapping sql=logic_mappings
  languageMappingId LanguageMappingId
  sourceId LogicId
  targetId LogicId
  slug String
  UniqueLanguageMappingIdLogicMappingSlug languageMappingId slug
  name String
  isInclusion Bool
  hasModelExpansion Bool
  isWeaklyAmalgamable Bool
  deriving Show

-- Not yet implemented in the Hets business logic
-- Serialization
--   slug String
--   UniqueSerializationSlug slug
--   languageId LanguageId
--   name String
--   deriving Show

Signature sql=signatures
  languageId LanguageId
  asJson String

SignatureMorphism sql=signature_morphisms
  logicMappingId LogicMappingId
  asJson String
  deriving Show

ConsStatus sql=cons_statuses
  -- Use "Unknown String" for non-Common.Consistency.Conservativtiy statuses
  required String
  proved String
  deriving Show


-- We leave out the other columns here because we don't need them in Hets
Repository sql=repositories
  slug String
  deriving Show

FileVersion sql=file_versions
  repositoryId RepositoryId
  commitSha String
  path String
  UniqueFileVersionInCommit repositoryId commitSha path
  deriving Show

LocIdBase sql=loc_id_bases
  fileVersionId FileVersionId -- FileVersionId is LocIdBaseId
  kind Enums.LocIdBaseKindType
  locId String
  UniqueLocIdBaseLocId fileVersionId kind locId
  deriving Show

Document sql=documents
  locIdBaseId LocIdBaseId sql=id -- the field `locIdBaseId` is mapped to the column `id`
  Primary locIdBaseId            -- ... which is the primary key
  kind DocumentKindType
  name String
  location String Maybe
  version String Maybe
  deriving Show

DocumentLink sql=document_links
  sourceId LocIdBaseId -- DocumentId is LocIdBaseId
  targetId LocIdBaseId -- DocumentId is LocIdBaseId
  deriving Show

Range sql=ranges
  path String
  startLine Int
  startColumn Int
  endLine Int Maybe
  endColumn Int Maybe
  deriving Show

Error sql=errors
  documentId LocIdBaseId -- DocumentId is LocIdBaseId
  rangeId RangeId Maybe
  number Int
  kind Enums.ErrorKindType
  text Text
  deriving Show

OMS sql=oms
  locIdBaseId LocIdBaseId sql=id -- the field `locIdBaseId` is mapped to the column `id`
  Primary locIdBaseId            -- ... which is the primary key
  documentId LocIdBaseId -- DocumentId is LocIdBaseId
  logicId LogicId
  languageId LanguageId
  -- Not yet implemented in Hets business logic:
  -- serializationId SerializationId
  signatureId SignatureId
  normalFormId LocIdBaseId Maybe
  normalFormSignatureMorphismId SignatureMorphismId Maybe
  freeNormalFormId LocIdBaseId Maybe
  freeNormalFormSignatureMorphismId SignatureMorphismId Maybe
  origin OMSOrigin
  consStatusId ConsStatusId
  nameRangeId RangeId Maybe -- Represents NodeName
  name String               -- Represents NodeName
  nameExtension String      -- Represents NodeName
  nameExtensionIndex Int    -- Represents NodeName
  labelHasHiding Bool
  labelHasFree Bool
  deriving Show

Mapping sql=mappings
  locIdBaseId LocIdBaseId sql=id -- the field `locIdBaseId` is mapped to the column `id`
  Primary locIdBaseId            -- ... which is the primary key
  sourceId LocIdBaseId -- OMSId is a LocIdBaseId
  targetId LocIdBaseId -- OMSId is a LocIdBaseId
  signatureMorphismId SignatureMorphismId
  consStatusId ConsStatusId Maybe

  -- Exactly one of the following two is not `Nothing`:
  freenessParameterOMSId LocIdBaseId Maybe sql=freeness_parameter_oms_id -- DocumentId is a LocIdBaseId
  freenessParameterLanguageId LanguageId Maybe

  name String
  origin MappingOrigin
  pending Bool
  type MappingType
  deriving Show

Sentence sql=sentences
  locIdBaseId LocIdBaseId sql=id -- the field `locIdBaseId` is mapped to the column `id`
  Primary locIdBaseId            -- ... which is the primary key
  omsId LocIdBaseId -- OMSId is LocIdBaseId
  rangeId RangeId Maybe
  kind SentenceKindType
  name String
  text Text
  deriving Show

Axiom sql=axioms
  -- the field `locIdBaseId` is mapped to the column `id`
  sentenceId LocIdBaseId sql=id -- SentenceId is LocIdBaseId
  Primary sentenceId -- ... which is the primary key
  deriving Show

Conjecture sql=conjectures
  -- the field `locIdBaseId` is mapped to the column `id`
  sentenceId LocIdBaseId sql=id -- SentenceId is LocIdBaseId
  Primary sentenceId -- ... which is the primary key
  kind ConjectureKindType
  evaluationState EvaluationStateType default='not_yet_enqueued'
  reasoningStatus ReasoningStatusOnConjectureType default='OPN'
  deriving Show

Symbol sql=symbols
  locIdBaseId LocIdBaseId sql=id -- the field `locIdBaseId` is mapped to the column `id`
  Primary locIdBaseId            -- ... which is the primary key
  omsId LocIdBaseId -- OMSId is LocIdBaseId
  rangeId RangeId Maybe
  symbolKind String
  name String
  fullName Text
  deriving Show

SentenceSymbol sql=sentences_symbols
  sentenceId LocIdBaseId -- SentenceId is LocIdBaseId
  symbolId LocIdBaseId -- SymbolId is LocIdBaseId
  Primary sentenceId symbolId
  deriving Show

SignatureSymbol sql=signature_symbols
  signatureId SignatureId
  symbolId LocIdBaseId -- SymbolId is LocIdBaseId
  Primary signatureId symbolId
  imported Bool
  deriving Show

Reasoner sql=reasoners
  slug String
  UniqueReasonerSlug
  displayName String
  deriving Show

ReasonerConfiguration sql=reasoner_configurations
  configuredReasonerId ReasonerId Maybe
  timeLimit Int
  deriving Show

PremiseSelection sql=premise_selections
  reasonerConfigurationId ReasonerConfigurationId
  deriving Show

PremiseSelectedAxioms sql=premise_selected_axioms
  axiomId LocIdBaseId -- AxiomId is LocIdBaseId
  premiseSelectionId PremiseSelectionId
  Primary axiomId premiseSelectionId
  deriving Show

ManualPremiseSelection sql=manual_premise_selections
  -- the field `premiseSelectionId` is mapped to the column `id`
  premiseSelectionId PremiseSelectionId sql=id
  Primary premiseSelectionId -- ... which is the primary key
  deriving Show

SinePremiseSelection sql=sine_premise_selections
  -- the field `premiseSelectionId` is mapped to the column `id`
  premiseSelectionId PremiseSelectionId sql=id
  Primary premiseSelectionId -- ... which is the primary key
  depthLimit Int Maybe
  tolerance Double Maybe
  axiomNumberLimit Int Maybe
  deriving Show

SineSymbolAxiomTrigger sql=sine_symbol_axiom_triggers
  -- SinePremiseSelectionId is PremiseSelectionId
  sinePremiseSelectionId PremiseSelectionId sql=id
  Primary sinePremiseSelectionId -- ... which is the primary key
  axiomId LocIdBaseId -- AxiomId is LocIdBaseId
  symbolId LocIdBaseId -- SymbolId is LocIdBaseId
  minTolerance Double
  deriving Show

SineSymbolCommonness sql=sine_symbol_commonnesses
  -- SinePremiseSelectionId is PremiseSelectionId
  sinePremiseSelectionId PremiseSelectionId sql=id
  Primary sinePremiseSelectionId -- ... which is the primary key
  symbolId LocIdBaseId -- SymbolId is LocIdBaseId
  commonness Int
  deriving Show

ReasoningAttempt sql=reasoning_attempts
  reasonerConfigurationId ReasonerConfigurationId
  usedReasonerId ReasonerId Maybe
  number Int
  timeTaken Int Maybe
  evaluationState EvaluationStateType default='not_yet_enqueued'
  reasoningStatus ReasoningStatusOnReasoningAttemptType default='OPN'
  deriving Show

GeneratedAxiom sql=generated_axioms
  reasoningAttemptId ReasoningAttemptId
  text Text
  deriving Show

ReasonerOutput
  reasoningAttemptId ReasoningAttemptId
  reasonerId ReasonerId
  text Text
  deriving Show
|]