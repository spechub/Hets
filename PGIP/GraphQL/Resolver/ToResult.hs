module PGIP.GraphQL.Resolver.ToResult where

import PGIP.GraphQL.Result.ConservativityStatus as GraphQLResultConservativityStatus
import PGIP.GraphQL.Result.FileRange as GraphQLResultFileRange
import PGIP.GraphQL.Result.IdReference (IdReference (..))
import PGIP.GraphQL.Result.Language as GraphQLResultLanguage
import PGIP.GraphQL.Result.LanguageMapping as GraphQLResultLanguageMapping
import PGIP.GraphQL.Result.LocIdReference (LocIdReference (..))
import PGIP.GraphQL.Result.LogicMapping as GraphQLResultLogicMapping
import PGIP.GraphQL.Result.Mapping as GraphQLResultMapping
import PGIP.GraphQL.Result.Serialization as GraphQLResultSerialization
import PGIP.GraphQL.Result.Signature as GraphQLResultSignature
import PGIP.GraphQL.Result.SignatureMorphism as GraphQLResultSignatureMorphism
import PGIP.GraphQL.Result.StringReference (StringReference (..))
import PGIP.GraphQL.Result.Symbol as GraphQLResultSymbol
import PGIP.GraphQL.Result.SymbolMapping as GraphQLResultSymbolMapping

import Persistence.Schema as DatabaseSchema

import qualified Data.Text as Text
import Database.Esqueleto

conservativityStatusToResult :: Entity DatabaseSchema.ConservativityStatus
                             -> GraphQLResultConservativityStatus.ConservativityStatus
conservativityStatusToResult (Entity _ conservativityStatusValue) =
  GraphQLResultConservativityStatus.ConservativityStatus
    { GraphQLResultConservativityStatus.required = conservativityStatusRequired conservativityStatusValue
    , GraphQLResultConservativityStatus.proved = conservativityStatusProved conservativityStatusValue
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
    { GraphQLResultLanguageMapping.id = fromIntegral $ fromSqlKey $ entityKey languageMappingEntity
    , GraphQLResultLanguageMapping.source = StringReference $ DatabaseSchema.languageSlug $ entityVal languageSource
    , GraphQLResultLanguageMapping.target = StringReference $ DatabaseSchema.languageSlug $ entityVal languageTarget
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
    , GraphQLResultLogicMapping.source = StringReference $ DatabaseSchema.logicSlug $ entityVal logicSource
    , GraphQLResultLogicMapping.target = StringReference $ DatabaseSchema.logicSlug $ entityVal logicTarget
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
        , GraphQLResultMapping.freenessParameterOMS = fmap (LocIdReference . locIdBaseLocId . entityVal) freenesParameterOMSLocIdM
        , GraphQLResultMapping.freenessParameterLanguage = freenessParameterLanguageResult
        , GraphQLResultMapping.locId = locIdBaseLocId $ entityVal mappingLocIdBase
        , GraphQLResultMapping.name = mappingName mappingValue
        , GraphQLResultMapping.origin = show $ mappingOrigin mappingValue
        , GraphQLResultMapping.pending = mappingPending mappingValue
        , GraphQLResultMapping.signatureMorphism = IdReference $ fromIntegral $ fromSqlKey signatureMorphismKey
        , GraphQLResultMapping.source = LocIdReference $ locIdBaseLocId $ entityVal locIdBaseSource
        , GraphQLResultMapping.target = LocIdReference $ locIdBaseLocId $ entityVal locIdBaseTarget
        , GraphQLResultMapping.mappingType = show $ DatabaseSchema.mappingType mappingValue
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
signatureToResult (Entity signatureKey _) omsL signatureMorphismsAsSourceL signatureMorphismsAsTargetL symbolsWithFileRanges =
  GraphQLResultSignature.Signature
    { GraphQLResultSignature.id = fromIntegral $ fromSqlKey signatureKey
    , GraphQLResultSignature.oms = map (LocIdReference . locIdBaseLocId . entityVal) omsL
    , GraphQLResultSignature.signatureMorphismsSource = map (IdReference . fromIntegral . fromSqlKey . entityKey) signatureMorphismsAsSourceL
    , GraphQLResultSignature.signatureMorphismsTarget = map (IdReference . fromIntegral . fromSqlKey . entityKey) signatureMorphismsAsTargetL
    , GraphQLResultSignature.symbols = map symbolToResultUncurried symbolsWithFileRanges
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
    { GraphQLResultSignatureMorphism.id = fromIntegral $ fromSqlKey signatureMorphismKey
    , GraphQLResultSignatureMorphism.logicMapping = logicMappingResult
    , GraphQLResultSignatureMorphism.mappings = mappingResults
    , GraphQLResultSignatureMorphism.source = IdReference $ fromIntegral $ fromSqlKey $ entityKey signatureSource
    , GraphQLResultSignatureMorphism.symbolMappings = symbolMappingResults
    , GraphQLResultSignatureMorphism.target = IdReference $ fromIntegral $ fromSqlKey $ entityKey signatureTarget
    }

symbolToResult :: Entity DatabaseSchema.LocIdBase
               -> Entity DatabaseSchema.Symbol
               -> Maybe (Entity DatabaseSchema.FileRange)
               -> GraphQLResultSymbol.Symbol
symbolToResult (Entity _ locIdBaseValue) (Entity _ symbolValue) fileRangeM =
  let fileRangeResult =
        fmap (\(Entity _ fileRangeValue) -> GraphQLResultFileRange.FileRange
               { GraphQLResultFileRange.startLine = fileRangeStartLine fileRangeValue
               , GraphQLResultFileRange.startColumn = fileRangeStartColumn fileRangeValue
               , GraphQLResultFileRange.endLine = fileRangeEndLine fileRangeValue
               , GraphQLResultFileRange.endColumn = fileRangeEndColumn fileRangeValue
               , GraphQLResultFileRange.path = fileRangePath fileRangeValue
               }) fileRangeM
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
    { GraphQLResultSymbolMapping.source = symbolToResultUncurried sourceSymbolData
    , GraphQLResultSymbolMapping.target = symbolToResultUncurried targetSymbolData
    }

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c
