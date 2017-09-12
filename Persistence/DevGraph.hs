{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE FlexibleContexts           #-}
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

module Persistence.DevGraph (exportLibEnv) where

import Persistence.Database
import Persistence.LogicGraph
import Persistence.Schema as SchemaClass hiding (ConsStatus, Range)
import Persistence.Schema.MappingOrigin (MappingOrigin)
import qualified Persistence.Schema.MappingOrigin as MappingOrigin
import Persistence.Range
import Persistence.Schema.MappingType (MappingType)
import qualified Persistence.Schema.ConjectureKindType as ConjectureKindType
import qualified Persistence.Schema.DocumentKindType as DocumentKindType
import qualified Persistence.Schema.Enums as Enums
import qualified Persistence.Schema.EvaluationStateType as EvaluationStateType
import qualified Persistence.Schema.MappingType as MappingType
import Persistence.Schema.OMSOrigin (OMSOrigin)
import qualified Persistence.Schema.OMSOrigin as OMSOrigin
import qualified Persistence.Schema.ReasoningStatusOnConjectureType as ReasoningStatusOnConjectureType
import qualified Persistence.Schema as SchemaClass (ConsStatus (..))
import qualified Persistence.Schema.SentenceKindType as SentenceKindType
import Persistence.Utils

import Common.AS_Annotation
import Common.Consistency
import Common.DocUtils
import Common.ExtSign
import Common.GlobalAnnotations
import Common.Id
import Common.Json (ppJson)
import Common.Lib.Graph as Graph hiding (nodeLabel)
import qualified Common.Lib.Graph as Graph (nodeLabel)
import Common.Lib.Rel (Rel)
import qualified Common.Lib.Rel as Rel
import Common.LibName
import Driver.Options
import qualified Common.OrderedMap as OMap
import Logic.Comorphism
import Logic.Grothendieck hiding (gMorphism)
import Logic.Logic as Logic
import Logic.Prover
import Static.DevGraph
import Static.DgUtils
import Static.GTheory
import qualified Static.ToJson as ToJson

import Control.Monad (foldM)
import Control.Monad.IO.Class (MonadIO (..))
import Data.Char (toLower)
import qualified Data.IntMap as IntMap
import Data.Graph.Inductive.Graph as Graph
import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text
import Database.Persist

import Debug.Trace

-- TODO: replace this by the `symbol` type variable and find a string representation that is unique such that there can be a unique index in the database
type SymbolMapIndex = (String, String) -- (SymbolKind, FullSymbolName)

data DBCache = DBCache { nodeMap :: Map Node LocIdBaseId
                       , theoryMap :: Map ThId OMSId
                       , signatureMap :: Map SigId SignatureId
                       , signatureMorphismMap :: Map MorId SignatureMorphismId
                       , symbolKeyMap :: Map SymbolMapIndex LocIdBaseId
                       } deriving Show
emptyDBCache :: DBCache
emptyDBCache = DBCache { nodeMap = Map.empty
                       , theoryMap = Map.empty
                       , signatureMap = Map.empty
                       , signatureMorphismMap = Map.empty
                       , symbolKeyMap = Map.empty
                       }

exportLibEnv :: HetcatsOpts -> LibEnv -> IO ()
exportLibEnv opts libEnv =
  onDatabase (databaseConfig opts) $ do
    migrateLanguages
    let dependencyLibNameRel = getLibDepRel libEnv
    let dependencyOrderedLibsSetL = Rel.depSort dependencyLibNameRel
    documentMap <- createDocuments opts libEnv dependencyOrderedLibsSetL
    createDocumentLinks documentMap dependencyLibNameRel
    return ()

createDocuments :: MonadIO m
                => HetcatsOpts -> LibEnv -> [Set LibName]
                -> DBMonad m (Map LibName LocIdBaseId)
createDocuments opts libEnv =
  foldM (\ outerAcc libNameSet ->
             foldM (\ innerAcc libName -> do
                      documentKey <- createDocument libName
                      return $ Map.insert libName documentKey innerAcc
                   ) outerAcc libNameSet
        ) Map.empty
  where
    createDocument :: MonadIO m
                   => LibName -> DBMonad m LocIdBaseId
    createDocument libName = do
      let name = show $ pretty $ getLibId libName
      let location = fmap show $ locIRI libName
      let version = fmap (intercalate "." . (\ (VersionNumber v _) -> v)) $ libVersion libName
      -- TODO: Use the correct locId
      let locId = name

      -- TODO: find the correct Repository
      repositoryM <- selectFirst [RepositorySlug ==. "ada/fixtures"] []
      case repositoryM of
        -- TODO: print the Repository id in the error
        Nothing -> fail "Did not find the Repository"
        Just (Entity repositoryKey _) -> do
          -- TODO: find the correct FileVersion
          fileVersionM <- selectFirst [FileVersionRepositoryId ==. repositoryKey] []
          case fileVersionM of
            -- TODO: print the FileVersion id in the error
            Nothing -> fail "Did not find the FileVersion"
            Just (Entity fileVersionKey _) ->
              let dGraph = fromJust $ Map.lookup libName libEnv
              in do
                  -- TODO: Check whether it is a Library or a NativeDocument
                  -- TODO: find a fitting locId
                  let documentLocIdBaseValue = LocIdBase
                        { locIdBaseFileVersionId = fileVersionKey
                        , locIdBaseKind = Enums.Library
                        , locIdBaseLocId = locId
                        }
                  documentKey <- insert documentLocIdBaseValue
                  insert Document
                    { documentLocIdBaseId = documentKey
                    , documentKind = DocumentKindType.NativeDocument
                    , documentName = name
                    , documentLocation = location
                    , documentVersion = version
                    }
                  createOMS opts dGraph fileVersionKey
                    (Entity documentKey documentLocIdBaseValue)
                  return documentKey

createDocumentLinks :: MonadIO m
                    => Map LibName LocIdBaseId -> Rel LibName
                    -> DBMonad m ()
createDocumentLinks documentMap dependencyLibNameRel =
  mapM_ (\ (targetLibName, sourceLibNamesSet) ->
          mapM_ (createDocumentLink targetLibName) $
            Set.toList sourceLibNamesSet
        ) $ Map.toList $ Rel.toMap dependencyLibNameRel
  where
    createDocumentLink :: MonadIO m
                       => LibName -> LibName -> DBMonad m ()
    createDocumentLink sourceLibName targetLibName = do
      -- These libNames must be in the documentMap by construction
      let sourceKey = fromJust $ Map.lookup sourceLibName documentMap
      let targetKey = fromJust $ Map.lookup targetLibName documentMap
      insert DocumentLink { documentLinkSourceId = sourceKey
                          , documentLinkTargetId = targetKey
                          }
      return ()

createOMS :: MonadIO m
          => HetcatsOpts -> DGraph -> FileVersionId -> Entity LocIdBase
          -> DBMonad m [LocIdBaseId]
createOMS opts dGraph fileVersionKey (Entity documentKey documentLocIdBaseValue) =
  let nodeLabels = labNodes $ dgBody dGraph
      linkLabels = labEdges $ dgBody dGraph
  in do
    (omsKeys, dbCache1) <-
      foldM (\ (omsKeyAcc, dbCacheAcc) nodeLabelWithId -> do
              (omsKey, newCache) <-
                findOrCreateNode dbCacheAcc nodeLabelWithId
              return (omsKey : omsKeyAcc, newCache)
            ) ([], emptyDBCache) nodeLabels
    mapM_ (createMapping dbCache1) linkLabels
    return omsKeys
  where
    globalAnnotations = globalAnnos dGraph

    findOrCreateNode :: MonadIO m
                     => DBCache -> (Int, DGNodeLab)
                     -> DBMonad m (LocIdBaseId, DBCache)
    findOrCreateNode dbCache (nodeId, nodeLabel) =
      let keyM = Map.lookup nodeId $ nodeMap dbCache in
      case keyM of
        Just key -> return (key, dbCache)
        Nothing -> do
          (normalFormKeyM, dbCache1) <- createNodeById dbCache $ dgn_nf nodeLabel
          (normalFormSignatureMorphismKeyM, dbCache2) <-
            findOrCreateSignatureMorphismM opts dbCache1 globalAnnotations $
              dgn_sigma nodeLabel
          (freeNormalFormKeyM, dbCache3) <- createNodeById dbCache2 $ dgn_freenf nodeLabel
          (freeNormalFormSignatureMorphismKeyM, dbCache4) <-
            findOrCreateSignatureMorphismM opts dbCache3 globalAnnotations $
              dgn_sigma nodeLabel
          case nodeInfo nodeLabel of
            DGNode _ consStatus -> do
              consStatusKey <- createConsStatus consStatus
              let internalNodeName = dgn_name nodeLabel
              nodeNameRangeKey <- createRange $ srcRange internalNodeName
              ----------------------------------------------------------------------
              -- TODO: Work with these
              -- [ ] gTheorySyntax is stored as an assoication to Serialization
              -- [ ] gTheorySignIdx, gTheorySelfIdx is the index of the theory in thMap above (use it to avoid duplicates)
              let gTheory = dgn_theory nodeLabel

              languageKey <- case gTheory of
                G_theory { gTheoryLogic = lid } -> findLanguage lid

              logicKey <- case sublogicOfTh gTheory of
                G_sublogics lid sublogics -> findLogic lid sublogics

              (signatureKey, dbCache5) <- case gTheory of
                G_theory { gTheoryLogic = lid
                         , gTheorySignIdx = sigId
                         , gTheorySign = extSign
                         } ->
                 findOrCreateSignature dbCache4 lid extSign sigId languageKey

              -- Not yet implemented in the Hets business logic
              -- syntaxId <- case gTheory of
              --               G_theory { gTheorySyntax = syntaxIRIM } ->
              --                 findOrCreateSyntax syntaxIRIM
              ----------------------------------------------------------------------
              let name = show $ getName internalNodeName
              let nameExtension = extString internalNodeName
              let nameExtensionIndex = extIndex internalNodeName
              let fullName = name ++ nameExtension ++ show nameExtensionIndex
              let omsLocIdBaseValue = LocIdBase
                    { locIdBaseFileVersionId = fileVersionKey
                    , locIdBaseKind = Enums.OMS
                    -- TODO: find a fitting locId
                    , locIdBaseLocId = fullName
                    }
              omsLocIdBaseKey <- insert omsLocIdBaseValue
              insert OMS
                { oMSLocIdBaseId = omsLocIdBaseKey
                , oMSDocumentId = documentKey
                , oMSLanguageId = languageKey
                , oMSLogicId = logicKey
                -- Not yet implemented in Hets business logic:
                -- , oMSSerializationId = undefined
                , oMSSignatureId = signatureKey
                , oMSNormalFormId = normalFormKeyM
                , oMSNormalFormSignatureMorphismId = normalFormSignatureMorphismKeyM
                , oMSFreeNormalFormId = freeNormalFormKeyM
                , oMSFreeNormalFormSignatureMorphismId = freeNormalFormSignatureMorphismKeyM
                , oMSOrigin = omsOrigin nodeLabel
                , oMSConsStatusId = consStatusKey
                , oMSNameRangeId = nodeNameRangeKey
                , oMSName = name
                , oMSNameExtension = nameExtension
                , oMSNameExtensionIndex = nameExtensionIndex
                , oMSLabelHasHiding = labelHasHiding nodeLabel
                , oMSLabelHasFree = labelHasFree nodeLabel
                }

              let omsLocIdBaseEntity = Entity omsLocIdBaseKey omsLocIdBaseValue

              dbCache6 <- case gTheory of
                G_theory { gTheoryLogic = lid
                         , gTheorySign = extSign
                         } -> createSymbols dbCache5 fileVersionKey
                                omsLocIdBaseEntity lid extSign

              (_, dbCache7) <- case gTheory of
                G_theory { gTheoryLogic = lid
                         , gTheorySign = ExtSign { plainSign = sign }
                         , gTheorySens = sentences
                         } -> createSentences dbCache6 omsLocIdBaseEntity
                                lid sign sentences

              dbCache8 <- case gTheory of
                G_theory { gTheoryLogic = lid
                         , gTheorySign = extSign
                         } -> associateSymbolsOfSignature dbCache7
                                lid extSign signatureKey

              let nodeMap' = Map.insert nodeId omsLocIdBaseKey $ nodeMap dbCache6
              return (omsLocIdBaseKey, dbCache8 { nodeMap = nodeMap' })
            DGRef { ref_node = refNodeId } -> do
              (omsLocIdBaseKeyM, dbCache5) <-
                createNodeById dbCache4 $ Just refNodeId
              -- `Nothing` cannot happen by construction:
              let omsLocIdBaseKey = fromJust omsLocIdBaseKeyM
              let nodeMap' = Map.insert nodeId omsLocIdBaseKey $ nodeMap dbCache5
              let dbCache6 = dbCache5 { nodeMap = nodeMap' }
              return (omsLocIdBaseKey, dbCache6)

    createSentences :: ( MonadIO m
                       , GetRange sentence
                       , Pretty sentence
                       , Sentences lid sentence sign morphism symbol
                       )
                    => DBCache -> Entity LocIdBase
                    -> lid -> sign
                    -> ThSens sentence (AnyComorphism, BasicProof)
                    -> DBMonad m ([LocIdBaseId], DBCache)
    createSentences dbCache omsLocId lid sign sentences =
      let (axioms, conjectures) = OMap.partition isAxiom sentences
          namedAxioms = toNamedList axioms
          orderedConjectures = OMap.toList conjectures
      in do
        (axiomKeys, dbCache1) <-
          foldM (\ (axiomKeysAcc, dbCacheAcc) namedAxiom -> do
                  (axiomKey, dbCacheAcc') <-
                    createAxiom dbCacheAcc omsLocId lid sign namedAxiom
                  associateSymbolsOfSentence dbCacheAcc axiomKey lid sign
                    namedAxiom
                  return (axiomKey : axiomKeysAcc, dbCacheAcc')
                ) ([], dbCache) namedAxioms
        (conjectureKeys, dbCache2) <-
          foldM (\ (conjectureKeysAcc, dbCacheAcc) (name, senStatus) ->
                  let namedConjecture = toNamed name senStatus
                      isProved = isProvenSenStatus senStatus
                  in do
                    (conjectureKey, dbCacheAcc') <- createConjecture dbCacheAcc
                                                      omsLocId lid sign isProved
                                                      namedConjecture
                    associateSymbolsOfSentence dbCacheAcc conjectureKey lid sign
                      namedConjecture
                    return (conjectureKey : conjectureKeysAcc, dbCacheAcc')
                ) ([], dbCache1) orderedConjectures
        return (conjectureKeys ++ axiomKeys, dbCache2)

    associateSymbolsOfSentence :: ( MonadIO m
                                  , GetRange sentence
                                  , Pretty sentence
                                  , Sentences lid sentence sign morphism symbol
                                  )
                               => DBCache
                               -> LocIdBaseId -> lid -> sign
                               -> Named sentence
                               -> DBMonad m DBCache
    associateSymbolsOfSentence dbCache sentenceKey lid sign namedSentence =
      let symbolsOfSentence = symsOfSen lid sign $ sentence namedSentence
      in  do
            foldM (\ associatedSymbols symbol ->
                    let fullName = show $ fullSymName lid symbol
                        mapIndex = symbolMapIndex lid symbol
                    in  if Set.member mapIndex associatedSymbols
                        then return associatedSymbols
                        else case Map.lookup mapIndex $ symbolKeyMap dbCache of
                               Just symbolKey -> do
                                 insert SentenceSymbol
                                   { sentenceSymbolSentenceId = sentenceKey
                                   , sentenceSymbolSymbolId = symbolKey
                                   }
                                 return $ Set.insert mapIndex associatedSymbols
                               Nothing -> fail ("Persistence.DevGraph.associateSymbolsOfSentence: Symbol not found: " ++ fullName)
                  ) Set.empty symbolsOfSentence
            return dbCache

    createAxiom :: ( MonadIO m
                   , GetRange sentence
                   , Pretty sentence
                   , Sentences lid sentence sign morphism symbol
                   )
                => DBCache -> Entity LocIdBase -> lid -> sign -> Named sentence
                -> DBMonad m (LocIdBaseId, DBCache)
    createAxiom dbCache (Entity omsKey omsLocIdBaseValue) lid sign namedAxiom =
      let name = senAttr namedAxiom
          range = getRangeSpan $ sentence namedAxiom
          locId = locIdBaseLocId omsLocIdBaseValue ++ "//" ++ name
          text = show $ useGlobalAnnos globalAnnotations $
                   print_named lid $ makeNamed "" $
                   simplify_sen lid sign $ sentence namedAxiom
      in do
          rangeKeyM <- createRange range
          axiomLocIdBaseKey <- insert LocIdBase
            { locIdBaseFileVersionId = fileVersionKey
            , locIdBaseKind = Enums.Axiom
            , locIdBaseLocId = locId
            }
          insert Sentence
            { sentenceLocIdBaseId = axiomLocIdBaseKey
            , sentenceOmsId = omsKey
            , sentenceRangeId = rangeKeyM
            , sentenceKind = SentenceKindType.Axiom
            , sentenceName = name
            , sentenceText = Text.pack text
            }
          insert Axiom
            { axiomSentenceId = axiomLocIdBaseKey
            }
          return (axiomLocIdBaseKey, dbCache)

    createConjecture :: ( MonadIO m
                        , GetRange sentence
                        , Pretty sentence
                        , Sentences lid sentence sign morphism symbol
                        )
                     => DBCache -> Entity LocIdBase -> lid -> sign -> Bool
                     -> Named sentence
                     -> DBMonad m (LocIdBaseId, DBCache)
    createConjecture dbCache (Entity omsKey omsLocIdBaseValue) lid sign isProved
                     namedConjecture =
      let name = senAttr namedConjecture
          range = getRangeSpan $ sentence namedConjecture
          locId = locIdBaseLocId omsLocIdBaseValue ++ "//" ++ name
          text = show $ useGlobalAnnos globalAnnotations $
                   print_named lid $ makeNamed "" $
                   simplify_sen lid sign $ sentence namedConjecture
          evaluationState =
            if isProved
            then EvaluationStateType.FinishedSuccessfully
            else EvaluationStateType.NotYetEnqueued
          kindLocId =
            if isProved
            then Enums.Theorem
            else Enums.OpenConjecture
          kindSentence =
            if isProved
            then SentenceKindType.Theorem
            else SentenceKindType.OpenConjecture
          kindConjecture =
            if isProved
            then ConjectureKindType.Theorem
            else ConjectureKindType.OpenConjecture
          reasoningStatus =
            if isProved
            then ReasoningStatusOnConjectureType.THM
            else ReasoningStatusOnConjectureType.OPN
      in do
          rangeKeyM <- createRange range
          conjectureLocIdBaseKey <- insert LocIdBase
            { locIdBaseFileVersionId = fileVersionKey
            , locIdBaseKind = kindLocId
            , locIdBaseLocId = locId
            }
          insert Sentence
            { sentenceLocIdBaseId = conjectureLocIdBaseKey
            , sentenceOmsId = omsKey
            , sentenceRangeId = rangeKeyM
            , sentenceKind = kindSentence
            , sentenceName = name
            , sentenceText = Text.pack text
            }
          insert Conjecture
            { conjectureSentenceId = conjectureLocIdBaseKey
            , conjectureKind = kindConjecture
            , conjectureEvaluationState = evaluationState
            , conjectureReasoningStatus = reasoningStatus
            }
          return (conjectureLocIdBaseKey, dbCache)

    createNodeById :: MonadIO m
                   => DBCache -> Maybe Node
                   -> DBMonad m (Maybe LocIdBaseId, DBCache)
    createNodeById dbCache nodeIdM = case nodeIdM of
      Nothing -> return (Nothing, dbCache)
      Just nodeId ->
        let nodeLabel = fromJust $ nodeLabelById nodeId
        in do
          (omsLocIdBaseKey, dbCache1) <-
            findOrCreateNode dbCache (nodeId, nodeLabel)
          return (Just omsLocIdBaseKey, dbCache1)

    nodeLabelById :: Node -> Maybe DGNodeLab
    nodeLabelById nodeId =
      fmap Graph.nodeLabel $ IntMap.lookup nodeId $ convertToMap $ dgBody dGraph

    omsOrigin :: DGNodeLab -> OMSOrigin
    omsOrigin nodeLabel = case node_origin $ nodeInfo nodeLabel of
      DGEmpty -> OMSOrigin.DGEmpty
      DGBasic -> OMSOrigin.DGBasic
      DGBasicSpec{} -> OMSOrigin.DGBasicSpec
      DGExtension -> OMSOrigin.DGExtension
      DGLogicCoercion -> OMSOrigin.DGLogicCoercion
      DGTranslation _ -> OMSOrigin.DGTranslation
      DGUnion -> OMSOrigin.DGUnion
      DGIntersect -> OMSOrigin.DGIntersect
      DGExtract -> OMSOrigin.DGExtract
      DGRestriction _ _ -> OMSOrigin.DGRestriction
      DGRevealTranslation -> OMSOrigin.DGRevealTranslation
      DGFreeOrCofree Free -> OMSOrigin.Free
      DGFreeOrCofree Cofree -> OMSOrigin.Cofree
      DGFreeOrCofree NPFree -> OMSOrigin.NPFree
      DGFreeOrCofree Minimize -> OMSOrigin.Minimize
      DGLocal -> OMSOrigin.DGLocal
      DGClosed -> OMSOrigin.DGClosed
      DGLogicQual -> OMSOrigin.DGLogicQual
      DGData -> OMSOrigin.DGData
      DGFormalParams -> OMSOrigin.DGFormalParams
      DGImports -> OMSOrigin.DGImports
      DGInst _ -> OMSOrigin.DGInst
      DGFitSpec -> OMSOrigin.DGFitSpec
      DGFitView _ -> OMSOrigin.DGFitView
      DGProof -> OMSOrigin.DGProof
      DGNormalForm _ -> OMSOrigin.DGNormalForm
      DGintegratedSCC -> OMSOrigin.DGintegratedSCC
      DGFlattening -> OMSOrigin.DGFlattening
      DGAlignment -> OMSOrigin.DGAlignment
      DGTest -> OMSOrigin.DGTest

    createMapping :: MonadIO m
                  => DBCache -> (Int, Int, DGLinkLab)
                  -> DBMonad m (LocIdBaseId, DBCache)
    createMapping dbCache (sourceId, targetId, linkLabel) = do
      sourceKey <- case Map.lookup sourceId $ nodeMap dbCache of
        Just key -> return key
        Nothing -> fail ("Persistence.DevGraph.createMapping: Could not find source node with ID " ++ show sourceId)

      targetKey <- case Map.lookup targetId $ nodeMap dbCache of
        Just key -> return key
        Nothing -> fail ("Persistence.DevGraph.createMapping: Could not find target node with ID " ++ show targetId)

      (signatureMorphismKey, dbCache1) <-
        findOrCreateSignatureMorphism opts dbCache globalAnnotations $
          dgl_morphism linkLabel

      let origin = mappingOriginOfLinkLabel linkLabel
      let mappingTypeValue = mappingTypeOfLinkLabel linkLabel

      consStatusKeyM <- case dgl_type linkLabel of
        ScopedLink _ _ consStatus -> fmap Just $ createConsStatus consStatus
        _ -> return Nothing

      freenessParameterOMSKeyM <- case dgl_type linkLabel of
        FreeOrCofreeDefLink _ (JustNode NodeSig { getNode = nodeId }) ->
          case Map.lookup nodeId $ nodeMap dbCache of
            Just key -> return $ Just key
            Nothing -> fail ("Persistence.DevGraph.createMapping: Could not find freeness parameter node with ID " ++ show nodeId)
        _ -> return Nothing

      freenessParameterLanguageKeyM <- case dgl_type linkLabel of
        FreeOrCofreeDefLink _ (EmptyNode (Logic.Logic lid)) ->
          fmap Just $ findLanguage lid
        _ -> return Nothing

      -- TODO: find a fitting locId
      let name = if null $ dglName linkLabel
                 then show (dgl_id linkLabel)
                 else dglName linkLabel
      let locId = locIdBaseLocId documentLocIdBaseValue ++ "//" ++ name
      mappingKey <- insert LocIdBase
        { locIdBaseFileVersionId = fileVersionKey
        , locIdBaseKind = Enums.Mapping
        , locIdBaseLocId = locId
        }
      insert Mapping
        { mappingLocIdBaseId = mappingKey
        , mappingSourceId = sourceKey
        , mappingTargetId = targetKey
        , mappingSignatureMorphismId = signatureMorphismKey
        , mappingConsStatusId = consStatusKeyM
        , mappingFreenessParameterOMSId = freenessParameterOMSKeyM
        , mappingFreenessParameterLanguageId = freenessParameterLanguageKeyM
        , mappingName = dglName linkLabel
        , mappingType = mappingTypeValue
        , mappingOrigin = origin
        , mappingPending = dglPending linkLabel
        }
      return (mappingKey, dbCache1)

    mappingOriginOfLinkLabel :: DGLinkLab -> MappingOrigin
    mappingOriginOfLinkLabel linkLabel = case dgl_origin linkLabel of
      SeeTarget -> MappingOrigin.SeeTarget
      SeeSource -> MappingOrigin.SeeSource
      TEST -> MappingOrigin.TEST
      DGLinkVerif -> MappingOrigin.DGLinkVerif
      DGImpliesLink -> MappingOrigin.DGImpliesLink
      DGLinkExtension -> MappingOrigin.DGLinkExtension
      DGLinkTranslation -> MappingOrigin.DGLinkTranslation
      DGLinkClosedLenv -> MappingOrigin.DGLinkClosedLenv
      DGLinkImports -> MappingOrigin.DGLinkImports
      DGLinkIntersect -> MappingOrigin.DGLinkIntersect
      DGLinkMorph _ -> MappingOrigin.DGLinkMorph
      DGLinkInst _ _ -> MappingOrigin.DGLinkInst
      DGLinkInstArg _ -> MappingOrigin.DGLinkInstArg
      DGLinkView _ _ -> MappingOrigin.DGLinkView
      DGLinkAlign _ -> MappingOrigin.DGLinkAlign
      DGLinkFitView _ -> MappingOrigin.DGLinkFitView
      DGLinkFitViewImp _ -> MappingOrigin.DGLinkFitViewImp
      DGLinkProof -> MappingOrigin.DGLinkProof
      DGLinkFlatteningUnion -> MappingOrigin.DGLinkFlatteningUnion
      DGLinkFlatteningRename -> MappingOrigin.DGLinkFlatteningRename
      DGLinkRefinement _ -> MappingOrigin.DGLinkRefinement

    mappingTypeOfLinkLabel :: DGLinkLab -> MappingType
    mappingTypeOfLinkLabel linkLabel = case dgl_type linkLabel of
      ScopedLink Local DefLink _ -> MappingType.LocalDef
      ScopedLink Local (ThmLink LeftOpen) _ -> MappingType.LocalThmOpen
      ScopedLink Local (ThmLink (Proven _ _)) _ -> MappingType.LocalThmProved
      ScopedLink Global DefLink _ -> MappingType.GlobalDef
      ScopedLink Global (ThmLink LeftOpen) _ -> MappingType.GlobalThmOpen
      ScopedLink Global (ThmLink (Proven _ _)) _ -> MappingType.GlobalThmProved
      HidingDefLink -> MappingType.HidingDef
      FreeOrCofreeDefLink Free _ -> MappingType.FreeDef
      FreeOrCofreeDefLink Cofree _ -> MappingType.CofreeDef
      FreeOrCofreeDefLink NPFree _ -> MappingType.NPFreeDef
      FreeOrCofreeDefLink Minimize _ -> MappingType.MinimizeDef
      HidingFreeOrCofreeThm Nothing _ _ LeftOpen -> MappingType.HidingOpen
      HidingFreeOrCofreeThm Nothing _ _ (Proven _ _) -> MappingType.HidingProved
      HidingFreeOrCofreeThm (Just Free) _ _ LeftOpen -> MappingType.HidingFreeOpen
      HidingFreeOrCofreeThm (Just Cofree) _ _ LeftOpen -> MappingType.HidingCofreeOpen
      HidingFreeOrCofreeThm (Just NPFree) _ _ LeftOpen -> MappingType.HidingNPFreeOpen
      HidingFreeOrCofreeThm (Just Minimize) _ _ LeftOpen -> MappingType.HidingMinimizeOpen
      HidingFreeOrCofreeThm (Just Free) _ _ (Proven _ _) -> MappingType.HidingFreeProved
      HidingFreeOrCofreeThm (Just Cofree) _ _ (Proven _ _) -> MappingType.HidingCofreeProved
      HidingFreeOrCofreeThm (Just NPFree) _ _ (Proven _ _) -> MappingType.HidingNPFreeProved
      HidingFreeOrCofreeThm (Just Minimize) _ _ (Proven _ _) -> MappingType.HidingMinimizeProved


findOrCreateSignatureMorphismM :: MonadIO m
                               => HetcatsOpts -> DBCache -> GlobalAnnos
                               -> Maybe GMorphism
                               -> DBMonad m ( Maybe SignatureMorphismId
                                            , DBCache
                                            )
findOrCreateSignatureMorphismM opts dbCache globalAnnotations gMorphismM =
  case gMorphismM of
    Nothing -> return (Nothing, dbCache)
    Just gMorphism -> do
      (signatureMorphismKey, dbCache1) <-
        findOrCreateSignatureMorphism opts dbCache globalAnnotations gMorphism
      return (Just signatureMorphismKey, dbCache1)

findOrCreateSignatureMorphism :: MonadIO m
                              => HetcatsOpts -> DBCache -> GlobalAnnos
                              -> GMorphism
                              -> DBMonad m ( SignatureMorphismId
                                           , DBCache
                                           )
findOrCreateSignatureMorphism opts dbCache globalAnnotations gMorphism =
  case gMorphism of
    GMorphism { gMorphismComor = cid
              , gMorphismMorIdx = morphismId
              } ->
      case Map.lookup morphismId $ signatureMorphismMap dbCache of
        Just key -> return (key, dbCache)
        Nothing ->
          let json = ppJson $ ToJson.gmorph opts globalAnnotations gMorphism
          in do
              (_, logicMappingKey) <-
                findOrCreateLanguageMappingAndLogicMapping $ Comorphism cid
              signatureMorphismKey <- insert SignatureMorphism
                { signatureMorphismLogicMappingId = logicMappingKey
                , signatureMorphismAsJson = json
                }
              let signatureMorphismMap' =
                    Map.insert morphismId signatureMorphismKey $
                      signatureMorphismMap dbCache
              return ( signatureMorphismKey
                     , dbCache { signatureMorphismMap = signatureMorphismMap' }
                     )

createConsStatus :: MonadIO m
                 => ConsStatus -> DBMonad m ConsStatusId
createConsStatus (ConsStatus r p _) =
  insert SchemaClass.ConsStatus
    { consStatusRequired = toString r
    , consStatusProved = toString p
    }
  where
    toString :: Conservativity -> String
    toString c = case c of
      Unknown s -> s
      _ -> map toLower $ show c

findLanguage :: ( MonadIO m
                , Logic.Logic lid sublogics
                    basic_spec sentence symb_items symb_map_items
                    sign morphism symbol raw_symbol proof_tree
                )
             => lid -> DBMonad m LanguageId
findLanguage lid = do
  languageM <- selectFirst [LanguageSlug ==. parameterize (show lid)] []
  case languageM of
    Just (Entity key _) -> return key
    Nothing -> fail ("Language not found in the database: " ++ show lid)

findLogic :: ( MonadIO m
             , Logic.Logic lid sublogics
                 basic_spec sentence symb_items symb_map_items
                 sign morphism symbol raw_symbol proof_tree
             )
          => lid -> sublogics -> DBMonad m LogicId
findLogic lid sublogic = do
  let name = sublogicName sublogic
  let logicSlugS = parameterize name
  languageKey <- findLanguage lid
  logicM <- selectFirst [ LogicLanguageId ==. languageKey
                        , LogicSlug ==. logicSlugS
                        ] []
  case logicM of
    Just (Entity key _) -> return key
    Nothing -> trace ("Logic not found in the database: " ++ logicSlugS ++ " (" ++ name ++ ")") $
      -- TODO: do not insert the sublogic as soon as https://github.com/spechub/Hets/issues/1740 is fixed
      insert SchemaClass.Logic
        { logicLanguageId = languageKey
        , logicSlug = logicSlugS
        , logicName = name
        }

findOrCreateSignature :: ( MonadIO m
                         , Sentences lid sentence sign morphism symbol
                         )
                      => DBCache -> lid -> ExtSign sign symbol -> SigId
                      -> LanguageId -> DBMonad m (SignatureId, DBCache)
findOrCreateSignature dbCache lid extSign sigId languageKey =
  case Map.lookup sigId $ signatureMap dbCache of
    Just signatureKey -> return (signatureKey, dbCache)
    Nothing -> do
      signatureKey <- insert Signature
        { signatureLanguageId = languageKey
        , signatureAsJson = ppJson $ ToJson.symbols lid extSign
        }
      return ( signatureKey
             , dbCache { signatureMap = Map.insert sigId signatureKey $
                                          signatureMap dbCache }
             )
associateSymbolsOfSignature :: ( MonadIO m
                               , Sentences lid sentence sign morphism symbol
                               )
                            => DBCache -> lid
                            -> ExtSign sign symbol -> SignatureId
                            -> DBMonad m DBCache
associateSymbolsOfSignature dbCache lid extSign signatureKey =
  let ownSymbols = nonImportedSymbols extSign
      allSymbols = symset_of lid $ plainSign extSign
  in do foldM (\ associatedSymbols symbol ->
                let mapIndex = symbolMapIndex lid symbol
                    symbolKey =
                      fromJust $ Map.lookup mapIndex $ symbolKeyMap dbCache
                    imported = Set.member symbol ownSymbols
                in  if Set.member mapIndex associatedSymbols
                    then return associatedSymbols
                    else do
                      insert SignatureSymbol
                        { signatureSymbolSignatureId = signatureKey
                        , signatureSymbolSymbolId = symbolKey
                        , signatureSymbolImported = imported
                        }
                      return $ Set.insert mapIndex associatedSymbols
              ) Set.empty allSymbols
        return dbCache

createSymbols :: ( MonadIO m
                 , Sentences lid sentence sign morphism symbol
                 )
              => DBCache -> FileVersionId -> Entity LocIdBase -> lid
              -> ExtSign sign symbol
              -> DBMonad m DBCache
createSymbols dbCache fileVersionKey (Entity omsKey omsLocIdBaseValue) lid
              (ExtSign { plainSign = sign }) = do
  symbolKeyMap' <-
    foldM (\ symbolKeyMapAcc symbol ->
            let name = show $ sym_name lid symbol
                fullName =
                  show $ fullSymName lid symbol
                symbolKind = symKind lid symbol
                locId = locIdBaseLocId omsLocIdBaseValue
                        ++ "//" ++ name
                mapIndex = symbolMapIndex lid symbol
            in case Map.lookup mapIndex symbolKeyMapAcc of
                 Just _ -> return symbolKeyMapAcc
                 Nothing -> do
                    symbolKey <- insert LocIdBase
                      { locIdBaseFileVersionId = fileVersionKey
                      , locIdBaseKind = Enums.Symbol
                      , locIdBaseLocId = locId
                      }
                    insert Symbol
                      { symbolLocIdBaseId = symbolKey
                      , symbolOmsId = omsKey
                      , symbolRangeId = Nothing
                      , symbolSymbolKind = symbolKind
                      , symbolName = name
                      , symbolFullName = Text.pack fullName
                      }
                    return $ Map.insert mapIndex symbolKey symbolKeyMapAcc
          ) Map.empty $ symlist_of lid sign
  return dbCache { symbolKeyMap = symbolKeyMap' }

symbolMapIndex :: Sentences lid sentence sign morphism symbol
               => lid -> symbol -> SymbolMapIndex
symbolMapIndex lid symbol =
  let fullName = show $ fullSymName lid symbol
      symbolKind = symKind lid symbol
  in (symbolKind, fullName)

-- Not yet implemented in the Hets business logic
-- findOrCreateSyntax syntax = return ()
