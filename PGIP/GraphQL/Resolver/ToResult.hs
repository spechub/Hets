module PGIP.GraphQL.Resolver.ToResult where

import PGIP.GraphQL.Result.Axiom as GraphQLResultAxiom
import PGIP.GraphQL.Result.Conjecture as GraphQLResultConjecture
import PGIP.GraphQL.Result.ConservativityStatus as GraphQLResultConservativityStatus
import PGIP.GraphQL.Result.DocumentLink as GraphQLResultDocumentLink
import PGIP.GraphQL.Result.FileRange as GraphQLResultFileRange
import PGIP.GraphQL.Result.IdReference (IdReference (..))
import PGIP.GraphQL.Result.Language as GraphQLResultLanguage
import PGIP.GraphQL.Result.LanguageMapping as GraphQLResultLanguageMapping
import PGIP.GraphQL.Result.Library as GraphQLResultLibrary
import PGIP.GraphQL.Result.LocIdReference (LocIdReference (..))
import PGIP.GraphQL.Result.Logic as GraphQLResultLogic
import PGIP.GraphQL.Result.LogicMapping as GraphQLResultLogicMapping
import PGIP.GraphQL.Result.Mapping as GraphQLResultMapping
import PGIP.GraphQL.Result.NativeDocument as GraphQLResultNativeDocument
import PGIP.GraphQL.Result.OMS as GraphQLResultOMS
import PGIP.GraphQL.Result.OMSSimple as GraphQLResultOMSSimple
import PGIP.GraphQL.Result.PremiseSelection as GraphQLResultPremiseSelection
import PGIP.GraphQL.Result.Reasoner as GraphQLResultReasoner
import PGIP.GraphQL.Result.ReasonerConfiguration as GraphQLResultReasonerConfiguration
import PGIP.GraphQL.Result.ReasonerOutput as GraphQLResultReasonerOutput
import PGIP.GraphQL.Result.ReasoningAttempt as GraphQLResultReasoningAttempt
import PGIP.GraphQL.Result.Sentence as GraphQLResultSentence
import PGIP.GraphQL.Result.Serialization as GraphQLResultSerialization
import PGIP.GraphQL.Result.Signature as GraphQLResultSignature
import PGIP.GraphQL.Result.SignatureMorphism as GraphQLResultSignatureMorphism
import PGIP.GraphQL.Result.StringReference (StringReference (..))
import PGIP.GraphQL.Result.Symbol as GraphQLResultSymbol
import PGIP.GraphQL.Result.SymbolMapping as GraphQLResultSymbolMapping

import Persistence.Schema as DatabaseSchema

import qualified Data.Text as Text
import Database.Esqueleto

axiomToResult :: Entity DatabaseSchema.Sentence
              -> Entity DatabaseSchema.LocIdBase
              -> Maybe (Entity DatabaseSchema.FileRange)
              -> [GraphQLResultSymbol.Symbol]
              -> GraphQLResultSentence.Sentence
axiomToResult (Entity _ sentenceValue) (Entity _ locIdBaseValue) fileRangeM symbolResults =
  GraphQLResultSentence.Axiom GraphQLResultAxiom.Axiom
    { GraphQLResultAxiom.__typename = "Axiom"
    , GraphQLResultAxiom.fileRange = fmap fileRangeToResult fileRangeM
    , GraphQLResultAxiom.locId = locIdBaseLocId locIdBaseValue
    , GraphQLResultAxiom.name = sentenceName sentenceValue
    , GraphQLResultAxiom.symbols = symbolResults
    , GraphQLResultAxiom.text = Text.unpack $ sentenceText sentenceValue
    }

conjectureToResult :: Entity DatabaseSchema.Sentence
                   -> Entity DatabaseSchema.LocIdBase
                   -> Maybe (Entity DatabaseSchema.FileRange)
                   -> Entity DatabaseSchema.Conjecture
                   -> [GraphQLResultSymbol.Symbol]
                   -> [GraphQLResultReasoningAttempt.ReasoningAttempt]
                   -> GraphQLResultSentence.Sentence
conjectureToResult (Entity _ sentenceValue) (Entity _ locIdBaseValue) fileRangeM
  (Entity _ conjectureValue) symbolResults proofAttemptResults =
  GraphQLResultSentence.Conjecture GraphQLResultConjecture.Conjecture
    { GraphQLResultConjecture.__typename = "Conjecture"
    , GraphQLResultConjecture.fileRange = fmap fileRangeToResult fileRangeM
    , GraphQLResultConjecture.locId = locIdBaseLocId locIdBaseValue
    , GraphQLResultConjecture.name = sentenceName sentenceValue
    , GraphQLResultConjecture.symbols = symbolResults
    , GraphQLResultConjecture.text = Text.unpack $ sentenceText sentenceValue
    , GraphQLResultConjecture.evaluationState =
        show $ conjectureEvaluationState conjectureValue
    , GraphQLResultConjecture.proofAttempts = proofAttemptResults
    , GraphQLResultConjecture.reasoningStatus =
        show $ conjectureReasoningStatus conjectureValue
    }

conservativityStatusToResult :: Entity DatabaseSchema.ConservativityStatus
                             -> GraphQLResultConservativityStatus.ConservativityStatus
conservativityStatusToResult (Entity _ conservativityStatusValue) =
  GraphQLResultConservativityStatus.ConservativityStatus
    { GraphQLResultConservativityStatus.required =
        conservativityStatusRequired conservativityStatusValue
    , GraphQLResultConservativityStatus.proved =
        conservativityStatusProved conservativityStatusValue
    }

documentLinkToResult :: Entity DatabaseSchema.LocIdBase
                     -> Entity DatabaseSchema.LocIdBase
                     -> GraphQLResultDocumentLink.DocumentLink
documentLinkToResult sourceLocId targetLocId =
  GraphQLResultDocumentLink.DocumentLink
    { GraphQLResultDocumentLink.source =
        LocIdReference $ locIdBaseLocId $ entityVal sourceLocId
    , GraphQLResultDocumentLink.target =
        LocIdReference $ locIdBaseLocId $ entityVal targetLocId
    }

fileRangeToResult :: Entity DatabaseSchema.FileRange
                  -> GraphQLResultFileRange.FileRange
fileRangeToResult (Entity _ fileRangeValue) =
  GraphQLResultFileRange.FileRange
     { GraphQLResultFileRange.startLine = fileRangeStartLine fileRangeValue
     , GraphQLResultFileRange.startColumn = fileRangeStartColumn fileRangeValue
     , GraphQLResultFileRange.endLine = fileRangeEndLine fileRangeValue
     , GraphQLResultFileRange.endColumn = fileRangeEndColumn fileRangeValue
     , GraphQLResultFileRange.path = fileRangePath fileRangeValue
     }

languageToResult :: Entity DatabaseSchema.Language
                 -> GraphQLResultLanguage.Language
languageToResult (Entity _ languageValue) =
  GraphQLResultLanguage.Language
    { GraphQLResultLanguage.id = languageSlug languageValue
    , GraphQLResultLanguage.name = languageName languageValue
    , GraphQLResultLanguage.description = languageDescription languageValue
    }

languageMappingToResult :: Entity DatabaseSchema.LanguageMapping
                        -> Entity DatabaseSchema.Language
                        -> Entity DatabaseSchema.Language
                        -> GraphQLResultLanguageMapping.LanguageMapping
languageMappingToResult languageMappingEntity languageSource languageTarget =
  GraphQLResultLanguageMapping.LanguageMapping
    { GraphQLResultLanguageMapping.id =
        fromIntegral $ fromSqlKey $ entityKey languageMappingEntity
    , GraphQLResultLanguageMapping.source =
        StringReference $ DatabaseSchema.languageSlug $ entityVal languageSource
    , GraphQLResultLanguageMapping.target =
        StringReference $ DatabaseSchema.languageSlug $ entityVal languageTarget
    }

libraryToResult :: Entity DatabaseSchema.Document
                -> Entity DatabaseSchema.LocIdBase
                -> [GraphQLResultDocumentLink.DocumentLink]
                -> [GraphQLResultDocumentLink.DocumentLink]
                -> [GraphQLResultOMSSimple.OMSSimple]
                -> GraphQLResultLibrary.Library
libraryToResult (Entity _ documentValue) (Entity _ locIdBaseValue)
  documentLinksSourceResults documentLinksTargetResults omsResults =
  GraphQLResultLibrary.Library
    { GraphQLResultLibrary.__typename = "Library"
    , GraphQLResultLibrary.displayName = documentDisplayName documentValue
    , GraphQLResultLibrary.locId = locIdBaseLocId locIdBaseValue
    , GraphQLResultLibrary.name = documentName documentValue
    , GraphQLResultLibrary.version = documentVersion documentValue
    , GraphQLResultLibrary.documentLinksSource = documentLinksSourceResults
    , GraphQLResultLibrary.documentLinksTarget = documentLinksTargetResults
    , GraphQLResultLibrary.omsList = omsResults
    }

logicToResult :: Entity DatabaseSchema.Logic
              -> GraphQLResultLogic.Logic
logicToResult (Entity _ logicValue) =
  GraphQLResultLogic.Logic
    { GraphQLResultLogic.id = logicSlug logicValue
    , GraphQLResultLogic.name = logicName logicValue
    }

logicMappingToResult :: Entity DatabaseSchema.LogicMapping
                     -> Entity DatabaseSchema.Logic
                     -> Entity DatabaseSchema.Logic
                     -> GraphQLResultLanguageMapping.LanguageMapping
                     -> GraphQLResultLogicMapping.LogicMapping
logicMappingToResult (Entity _ logicMappingValue) logicSource logicTarget languageMappingResult =
  GraphQLResultLogicMapping.LogicMapping
    { GraphQLResultLogicMapping.id = DatabaseSchema.logicMappingSlug logicMappingValue
    , GraphQLResultLogicMapping.languageMapping = languageMappingResult
    , GraphQLResultLogicMapping.source =
        StringReference $ DatabaseSchema.logicSlug $ entityVal logicSource
    , GraphQLResultLogicMapping.target =
        StringReference $ DatabaseSchema.logicSlug $ entityVal logicTarget
    }

mappingToResult :: Entity DatabaseSchema.Mapping
                -> Entity DatabaseSchema.LocIdBase
                -> Entity DatabaseSchema.SignatureMorphism
                -> Maybe (Entity DatabaseSchema.ConservativityStatus)
                -> Entity DatabaseSchema.LocIdBase -- The source OMS
                -> Entity DatabaseSchema.LocIdBase -- The target OMS
                -> Maybe (Entity DatabaseSchema.LocIdBase)
                -> Maybe (Entity DatabaseSchema.Language)
                -> GraphQLResultMapping.Mapping
mappingToResult (Entity _ mappingValue) mappingLocIdBase (Entity signatureMorphismKey _)
  conservativityStatusM locIdBaseSource locIdBaseTarget
  freenesParameterOMSLocIdM freenessParameterLanguageM =
  let conservativityStatusResult = fmap conservativityStatusToResult conservativityStatusM
      freenessParameterLanguageResult = fmap languageToResult freenessParameterLanguageM
  in  GraphQLResultMapping.Mapping
        { GraphQLResultMapping.conservativityStatus = conservativityStatusResult
        , GraphQLResultMapping.displayName = mappingDisplayName mappingValue
        , GraphQLResultMapping.freenessParameterOMS =
            fmap (LocIdReference . locIdBaseLocId . entityVal)
            freenesParameterOMSLocIdM
        , GraphQLResultMapping.freenessParameterLanguage =
            freenessParameterLanguageResult
        , GraphQLResultMapping.locId = locIdBaseLocId $ entityVal mappingLocIdBase
        , GraphQLResultMapping.name = mappingName mappingValue
        , GraphQLResultMapping.origin = show $ mappingOrigin mappingValue
        , GraphQLResultMapping.pending = mappingPending mappingValue
        , GraphQLResultMapping.signatureMorphism =
            IdReference $ fromIntegral $ fromSqlKey signatureMorphismKey
        , GraphQLResultMapping.source =
            LocIdReference $ locIdBaseLocId $ entityVal locIdBaseSource
        , GraphQLResultMapping.target =
            LocIdReference $ locIdBaseLocId $ entityVal locIdBaseTarget
        , GraphQLResultMapping.mappingType =
            show $ DatabaseSchema.mappingType mappingValue
        }

nativeDocumentToResult :: Entity DatabaseSchema.Document
                       -> Entity DatabaseSchema.LocIdBase
                       -> [GraphQLResultDocumentLink.DocumentLink]
                       -> [GraphQLResultDocumentLink.DocumentLink]
                       -> GraphQLResultOMSSimple.OMSSimple
                       -> GraphQLResultNativeDocument.NativeDocument
nativeDocumentToResult (Entity _ documentValue) (Entity _ locIdBaseValue)
  documentLinksSourceResults documentLinksTargetResults omsResult =
  GraphQLResultNativeDocument.NativeDocument
    { GraphQLResultNativeDocument.__typename = "NativeDocument"
    , GraphQLResultNativeDocument.displayName = documentDisplayName documentValue
    , GraphQLResultNativeDocument.locId = locIdBaseLocId locIdBaseValue
    , GraphQLResultNativeDocument.name = documentName documentValue
    , GraphQLResultNativeDocument.version = documentVersion documentValue
    , GraphQLResultNativeDocument.documentLinksSource = documentLinksSourceResults
    , GraphQLResultNativeDocument.documentLinksTarget = documentLinksTargetResults
    , GraphQLResultNativeDocument.oms = omsResult
    }

omsToResult :: Entity DatabaseSchema.OMS
            -> Entity DatabaseSchema.LocIdBase
            -> Entity DatabaseSchema.ConservativityStatus
            -> Maybe (Entity DatabaseSchema.FileRange)
            -> Maybe (Entity DatabaseSchema.LocIdBase)
            -> Maybe (Entity DatabaseSchema.SignatureMorphism)
            -> Entity DatabaseSchema.Language
            -> Entity DatabaseSchema.Logic
            -> Maybe (Entity DatabaseSchema.LocIdBase)
            -> Maybe (Entity DatabaseSchema.SignatureMorphism)
            -> [GraphQLResultReasoningAttempt.ReasoningAttempt]
            -> [GraphQLResultMapping.Mapping]
            -> [GraphQLResultMapping.Mapping]
            -> [GraphQLResultSentence.Sentence]
            -> Maybe StringReference
            -> GraphQLResultOMS.OMS
omsToResult (Entity _ omsValue) locIdBaseOMS conservativityStatusEntity
  fileRangeM freeNormalFormLocIdBaseM freeNormalFormSignatureMorphismM
  languageEntity logicEntity
  normalFormLocIdBaseM normalFormSignatureMorphismM
  consistencyCheckAttemptResults mappingSourceResults mappingTargetResults sentenceResults
  serializationResult =
  let conservativityStatusResult = conservativityStatusToResult conservativityStatusEntity
      fileRangeResult = fmap fileRangeToResult fileRangeM
  in  GraphQLResultOMS.OMS
        { GraphQLResultOMS.conservativityStatus = conservativityStatusResult
        , GraphQLResultOMS.consistencyCheckAttempts = consistencyCheckAttemptResults
        , GraphQLResultOMS.description = Nothing
        , GraphQLResultOMS.displayName = oMSDisplayName omsValue
        , GraphQLResultOMS.freeNormalForm =
            fmap (LocIdReference . locIdBaseLocId . entityVal) freeNormalFormLocIdBaseM
        , GraphQLResultOMS.freeNormalFormSignatureMorphism =
            fmap (IdReference . fromIntegral . fromSqlKey . entityKey)
            freeNormalFormSignatureMorphismM
        , GraphQLResultOMS.labelHasFree = oMSLabelHasFree omsValue
        , GraphQLResultOMS.labelHasHiding = oMSLabelHasHiding omsValue
        , GraphQLResultOMS.language = languageToResult languageEntity
        , GraphQLResultOMS.locId = locIdBaseLocId $ entityVal locIdBaseOMS
        , GraphQLResultOMS.logic = logicToResult logicEntity
        , GraphQLResultOMS.mappingsSource = mappingSourceResults
        , GraphQLResultOMS.mappingsTarget = mappingTargetResults
        , GraphQLResultOMS.name = oMSName omsValue
        , GraphQLResultOMS.nameExtension = oMSNameExtension omsValue
        , GraphQLResultOMS.nameExtensionIndex = oMSNameExtensionIndex omsValue
        , GraphQLResultOMS.nameFileRange = fileRangeResult
        , GraphQLResultOMS.normalForm =
            fmap (LocIdReference . locIdBaseLocId . entityVal) normalFormLocIdBaseM
        , GraphQLResultOMS.normalFormSignatureMorphism =
            fmap (IdReference . fromIntegral . fromSqlKey . entityKey)
            normalFormSignatureMorphismM
        , GraphQLResultOMS.origin = show $ oMSOrigin omsValue
        , GraphQLResultOMS.sentences = sentenceResults
        , GraphQLResultOMS.serialization = serializationResult
        , GraphQLResultOMS.omsSignature =
            IdReference $ fromIntegral $ fromSqlKey $ oMSSignatureId omsValue
        }

omsToResultSimple :: Entity DatabaseSchema.OMS
                  -> Entity DatabaseSchema.LocIdBase
                  -> GraphQLResultOMSSimple.OMSSimple
omsToResultSimple (Entity _ omsValue) (Entity _ locIdBaseValue) =
  GraphQLResultOMSSimple.OMSSimple
    { GraphQLResultOMSSimple.description = Nothing
    , GraphQLResultOMSSimple.displayName = oMSDisplayName omsValue
    , GraphQLResultOMSSimple.labelHasFree = oMSLabelHasFree omsValue
    , GraphQLResultOMSSimple.labelHasHiding = oMSLabelHasHiding omsValue
    , GraphQLResultOMSSimple.locId = locIdBaseLocId locIdBaseValue
    , GraphQLResultOMSSimple.name = oMSName omsValue
    , GraphQLResultOMSSimple.nameExtension = oMSNameExtension omsValue
    , GraphQLResultOMSSimple.nameExtensionIndex = oMSNameExtensionIndex omsValue
    , GraphQLResultOMSSimple.origin = show $ oMSOrigin omsValue
    }

premiseSelectionToResult :: [Entity DatabaseSchema.LocIdBase] -- Of Sentence
                         -> GraphQLResultPremiseSelection.PremiseSelection
premiseSelectionToResult premises =
  GraphQLResultPremiseSelection.PremiseSelection
    { GraphQLResultPremiseSelection.selectedPremises =
        map (LocIdReference . locIdBaseLocId . entityVal) premises
    }

reasonerToResult :: Entity DatabaseSchema.Reasoner
                 -> GraphQLResultReasoner.Reasoner
reasonerToResult (Entity _ reasonerValue) =
  GraphQLResultReasoner.Reasoner
    { GraphQLResultReasoner.id = reasonerSlug reasonerValue
    , GraphQLResultReasoner.displayName = reasonerDisplayName reasonerValue
    }

reasonerConfigurationToResult :: Entity DatabaseSchema.ReasonerConfiguration
                              -> Maybe (Entity DatabaseSchema.Reasoner)
                              -> [GraphQLResultPremiseSelection.PremiseSelection]
                              -> GraphQLResultReasonerConfiguration.ReasonerConfiguration
reasonerConfigurationToResult (Entity reasonerConfigurationKey
  reasonerConfigurationValue) reasonerM premiseSelectionResults =
  GraphQLResultReasonerConfiguration.ReasonerConfiguration
    { GraphQLResultReasonerConfiguration.configuredReasoner =
        fmap reasonerToResult reasonerM
    , GraphQLResultReasonerConfiguration.id =
        fromIntegral $ fromSqlKey reasonerConfigurationKey
    , GraphQLResultReasonerConfiguration.premiseSelections =
        premiseSelectionResults
    , GraphQLResultReasonerConfiguration.timeLimit =
        reasonerConfigurationTimeLimit reasonerConfigurationValue
    }

reasonerOutputToResult :: Entity DatabaseSchema.ReasonerOutput
                       -> GraphQLResultReasonerOutput.ReasonerOutput
reasonerOutputToResult (Entity _ reasonerOutputValue) =
  GraphQLResultReasonerOutput.ReasonerOutput
    { GraphQLResultReasonerOutput.text =
        Text.unpack $ reasonerOutputText reasonerOutputValue
    }

reasoningAttemptToResult :: Entity DatabaseSchema.ReasoningAttempt
                         -> Maybe (Entity DatabaseSchema.ReasonerOutput)
                         -> Maybe (Entity DatabaseSchema.Reasoner)
                         -> GraphQLResultReasonerConfiguration.ReasonerConfiguration
                         -> GraphQLResultReasoningAttempt.ReasoningAttempt
reasoningAttemptToResult (Entity _ reasoningAttemptValue) reasonerOutputEntity
  reasonerEntityM reasonerConfigurationResult =
  GraphQLResultReasoningAttempt.ReasoningAttempt
    { GraphQLResultReasoningAttempt.evaluationState =
        show $ reasoningAttemptEvaluationState reasoningAttemptValue
    , GraphQLResultReasoningAttempt.reasonerOutput =
        fmap reasonerOutputToResult reasonerOutputEntity
    , GraphQLResultReasoningAttempt.reasonerConfiguration =
        reasonerConfigurationResult
    , GraphQLResultReasoningAttempt.reasoningStatus =
        show $ reasoningAttemptReasoningStatus reasoningAttemptValue
    , GraphQLResultReasoningAttempt.timeTaken =
        reasoningAttemptTimeTaken reasoningAttemptValue
    , GraphQLResultReasoningAttempt.usedReasoner =
        fmap reasonerToResult reasonerEntityM
    }

serializationToResult :: Entity DatabaseSchema.Serialization
                      -> Entity DatabaseSchema.Language
                      -> GraphQLResultSerialization.Serialization
serializationToResult (Entity _ serializationValue) languageEntity =
  let languageResult = languageToResult languageEntity
  in GraphQLResultSerialization.Serialization
        { GraphQLResultSerialization.id = serializationSlug serializationValue
        , GraphQLResultSerialization.language = languageResult
        , GraphQLResultSerialization.name = serializationName serializationValue
        }

signatureToResult :: Entity DatabaseSchema.Signature
                  -> [Entity DatabaseSchema.LocIdBase] -- Of the OMS with this signature
                  -> [Entity DatabaseSchema.SignatureMorphism]
                  -> [Entity DatabaseSchema.SignatureMorphism]
                  -> [( Entity DatabaseSchema.LocIdBase
                      , Entity DatabaseSchema.Symbol
                      , Maybe (Entity DatabaseSchema.FileRange)
                      )]
                  -> GraphQLResultSignature.Signature
signatureToResult (Entity signatureKey _) omsL signatureMorphismsAsSourceL
  signatureMorphismsAsTargetL symbolsWithFileRanges =
  GraphQLResultSignature.Signature
    { GraphQLResultSignature.id = fromIntegral $ fromSqlKey signatureKey
    , GraphQLResultSignature.oms =
        map (LocIdReference . locIdBaseLocId . entityVal) omsL
    , GraphQLResultSignature.signatureMorphismsSource =
        map (IdReference . fromIntegral . fromSqlKey . entityKey)
        signatureMorphismsAsSourceL
    , GraphQLResultSignature.signatureMorphismsTarget =
        map (IdReference . fromIntegral . fromSqlKey . entityKey)
        signatureMorphismsAsTargetL
    , GraphQLResultSignature.symbols =
        map symbolToResultUncurried symbolsWithFileRanges
    }

signatureMorphismToResult :: Entity DatabaseSchema.SignatureMorphism
                          -> Entity DatabaseSchema.Signature
                          -> Entity DatabaseSchema.Signature
                          -> GraphQLResultLogicMapping.LogicMapping
                          -> [GraphQLResultMapping.Mapping]
                          -> [GraphQLResultSymbolMapping.SymbolMapping]
                          -> GraphQLResultSignatureMorphism.SignatureMorphism
signatureMorphismToResult (Entity signatureMorphismKey _) signatureSource
  signatureTarget logicMappingResult mappingResults symbolMappingResults =
  GraphQLResultSignatureMorphism.SignatureMorphism
    { GraphQLResultSignatureMorphism.id =
        fromIntegral $ fromSqlKey signatureMorphismKey
    , GraphQLResultSignatureMorphism.logicMapping = logicMappingResult
    , GraphQLResultSignatureMorphism.mappings = mappingResults
    , GraphQLResultSignatureMorphism.source =
        IdReference $ fromIntegral $ fromSqlKey $ entityKey signatureSource
    , GraphQLResultSignatureMorphism.symbolMappings = symbolMappingResults
    , GraphQLResultSignatureMorphism.target =
        IdReference $ fromIntegral $ fromSqlKey $ entityKey signatureTarget
    }

symbolToResult :: Entity DatabaseSchema.LocIdBase
               -> Entity DatabaseSchema.Symbol
               -> Maybe (Entity DatabaseSchema.FileRange)
               -> GraphQLResultSymbol.Symbol
symbolToResult (Entity _ locIdBaseValue) (Entity _ symbolValue) fileRangeM =
  let fileRangeResult = fmap fileRangeToResult fileRangeM
  in  GraphQLResultSymbol.Symbol
        { GraphQLResultSymbol.__typename = "Symbol"
        , GraphQLResultSymbol.fileRange = fileRangeResult
        , GraphQLResultSymbol.fullName = Text.unpack $ symbolFullName symbolValue
        , GraphQLResultSymbol.kind = symbolSymbolKind symbolValue
        , GraphQLResultSymbol.locId = locIdBaseLocId locIdBaseValue
        , GraphQLResultSymbol.name = symbolName symbolValue
        }

symbolToResultUncurried :: ( Entity DatabaseSchema.LocIdBase
                           , Entity DatabaseSchema.Symbol
                           , Maybe (Entity DatabaseSchema.FileRange)
                           ) -> GraphQLResultSymbol.Symbol
symbolToResultUncurried = uncurry3 symbolToResult

symbolMappingToResult :: ( Entity DatabaseSchema.LocIdBase
                         , Entity DatabaseSchema.Symbol
                         , Maybe (Entity DatabaseSchema.FileRange)
                         )
                      -> ( Entity DatabaseSchema.LocIdBase
                         , Entity DatabaseSchema.Symbol
                         , Maybe (Entity DatabaseSchema.FileRange)
                         )
                      -> GraphQLResultSymbolMapping.SymbolMapping
symbolMappingToResult sourceSymbolData targetSymbolData =
  GraphQLResultSymbolMapping.SymbolMapping
    { GraphQLResultSymbolMapping.source =
        symbolToResultUncurried sourceSymbolData
    , GraphQLResultSymbolMapping.target =
        symbolToResultUncurried targetSymbolData
    }

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c
