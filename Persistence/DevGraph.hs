{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
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
import Persistence.Diagnosis
import Persistence.FileVersion
import Persistence.LogicGraph
import Persistence.Schema as SchemaClass
import Persistence.Schema.MappingOrigin (MappingOrigin)
import qualified Persistence.Schema.MappingOrigin as MappingOrigin
import Persistence.Range
import Persistence.Schema.MappingType (MappingType)
import qualified Persistence.Schema.Enums as Enums
import qualified Persistence.Schema.EvaluationStateType as EvaluationStateType
import qualified Persistence.Schema.MappingType as MappingType
import Persistence.Schema.OMSOrigin (OMSOrigin)
import qualified Persistence.Schema.OMSOrigin as OMSOrigin
import qualified Persistence.Schema.ReasoningStatusOnConjectureType as ReasoningStatusOnConjectureType
import Persistence.Utils

import Common.AS_Annotation
import Common.Consistency
import Common.DocUtils
import Common.ExtSign
import Common.FileType
import Common.GlobalAnnotations
import Common.Id
import Common.IRI (IRI (..), setAngles)
import Common.Json (ppJson)
import Common.Lib.Graph as Graph hiding (nodeLabel)
import qualified Common.Lib.Graph as Graph (nodeLabel)
import Common.Lib.Rel (Rel)
import qualified Common.Lib.Rel as Rel
import Common.LibName
import Common.Result (maybeResult, Diagnosis(..), DiagKind(..))
import Common.ResultT (runResultT)
import Common.Utils
import Driver.Options
import qualified Common.OrderedMap as OMap
import Logic.Comorphism
import Logic.Grothendieck hiding (gMorphism)
import Logic.Logic as Logic
import Logic.Prover
import Static.DevGraph hiding (getLogic)
import Static.DgUtils
import Static.GTheory
import qualified Static.ToJson as ToJson

import Control.Exception
import Control.Monad (foldM, foldM_, when)
import Control.Monad.IO.Class (MonadIO (..))
import Data.Char (toLower)
import qualified Data.IntMap as IntMap
import Data.Graph.Inductive.Graph as Graph
import Data.List (intercalate, isPrefixOf, stripPrefix)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text
import Database.Persist
import Database.Persist.Sql

-- TODO: replace this by the `symbol` type variable and find a string representation that is unique such that there can be a unique index in the database
type SymbolMapIndex = (String, String) -- (SymbolKind, FullSymbolName)

data DBCache = DBCache
  { documentMap :: Map LibName LocIdBaseId -- Here, LocIdBaseId is DocumentId
  , nodeMap :: Map (LibName, Node) (LocIdBaseId, SignatureId) -- Here, LocIdBaseId is OMSId
  , signatureMap :: Map (LibName, SigId) SignatureId
  , signatureMorphismMap :: Map (LibName, MorId)
                             (SignatureMorphismId, [SymbolMappingId], GMorphism)
  , symbolKeyMap :: Map (LibName, Int, SymbolMapIndex) LocIdBaseId -- Here, LocIdBaseId is SymbolId
  } deriving Show

emptyDBCache :: DBCache
emptyDBCache = DBCache { documentMap = Map.empty
                       , nodeMap = Map.empty
                       , signatureMap = Map.empty
                       , signatureMorphismMap = Map.empty
                       , symbolKeyMap = Map.empty
                       }

exportLibEnv :: HetcatsOpts -> LibEnv -> IO ()
exportLibEnv opts libEnv = do
  onDatabase dbConfig $
    setFileVersionState dbContext EvaluationStateType.Processing
  Control.Exception.catch export saveErrorAndRethrow
  where
    dbConfig = databaseConfig opts
    dbContext = databaseContext opts

    export :: IO ()
    export = onDatabase dbConfig $ do
      let dependencyLibNameRel = getLibDepRel libEnv
      let dependencyOrderedLibsSetL = Rel.depSort dependencyLibNameRel
      dbCache1 <-
        createDocuments opts libEnv emptyDBCache dependencyOrderedLibsSetL
      createDocumentLinks dbCache1 dependencyLibNameRel
      setFileVersionState dbContext EvaluationStateType.FinishedSuccessfully
      return ()

    saveErrorAndRethrow :: SomeException -> IO ()
    saveErrorAndRethrow exception = do
      let message = show exception
      saveDiagnoses dbConfig dbContext 5 [Diag { diagKind = Error
                                               , diagString = message
                                               , diagPos = nullRange
                                               }]
      fail message

createDocuments :: MonadIO m
                => HetcatsOpts -> LibEnv -> DBCache -> [Set LibName]
                -> DBMonad m DBCache
createDocuments opts libEnv dbCache0 dependencyOrderedLibsSetL = do
  fileVersion <- getFileVersion $ databaseContext opts
  dbCache1 <-
    createDocumentsInDependencyRelation opts libEnv fileVersion dbCache0 $
      reverse dependencyOrderedLibsSetL
  createDocumentsThatAreIndependent opts libEnv fileVersion dbCache1

createDocumentsInDependencyRelation :: MonadIO m
                                    => HetcatsOpts -> LibEnv
                                    -> Entity FileVersion -> DBCache -> [Set LibName]
                                    -> DBMonad m DBCache
createDocumentsInDependencyRelation opts libEnv fileVersion =
  foldM
    (\ outerAcc libNameSet ->
       foldM
         (\ dbCacheAcc libName ->
            createDocument opts libEnv fileVersion dbCacheAcc libName
         ) outerAcc libNameSet
    )

createDocumentsThatAreIndependent :: MonadIO m
                                  => HetcatsOpts -> LibEnv
                                  -> Entity FileVersion -> DBCache
                                  -> DBMonad m DBCache
createDocumentsThatAreIndependent opts libEnv fileVersion dbCache =
  foldM
    (\ dbCacheAcc libName ->
      let alreadyInserted = isJust $ Map.lookup libName $ documentMap dbCacheAcc
      in  if alreadyInserted
          then return dbCacheAcc
          else createDocument opts libEnv fileVersion dbCacheAcc libName
    ) dbCache $ Map.keys libEnv

createDocument :: MonadIO m
               => HetcatsOpts -> LibEnv -> Entity FileVersion -> DBCache
               -> LibName -> DBMonad m DBCache
createDocument opts libEnv parentFileVersion dbCache0 libName =
  let dGraph = fromJust $ Map.lookup libName libEnv
      globalAnnotations = globalAnnos dGraph
      name = show $ pretty $ getLibId libName
      displayName = show $ setAngles False $ getLibId libName
      location = fmap show $ locIRI libName
      version = fmap (intercalate "." . (\ (VersionNumber v _) -> v)) $
                  libVersion libName
      locId = locIdOfDocument opts location displayName
  in  do
        -- We need to find the FileVersion of the corresponding document
        -- if it is located inside the libdir.
        fileVersionKey <- findFileVersionByPath opts parentFileVersion location
        kind <- kindOfDocument opts location
        let fileVersionKeyS =
              show $ unSqlBackendKey $ unFileVersionKey fileVersionKey
        advisoryLocked opts (fileVersionKeyS ++ "-" ++ show kind ++ "-" ++ locId) $ do
          documentM <- selectFirst [ LocIdBaseLocId ==. locId
                                   , LocIdBaseFileVersionId ==. fileVersionKey
                                   , LocIdBaseKind ==. kind
                                   ] []
          case documentM of
            Just (Entity documentKey _) ->
              when (databaseReanalyze opts) $ delete documentKey
            Nothing -> return ()
          (doSave, documentKey, documentLocIdBaseValue) <-
            case (databaseReanalyze opts, documentM) of
              (False, Just (Entity documentKey documentLocIdBaseValue)) ->
                return (False, documentKey, documentLocIdBaseValue)
              _ -> do
                let documentLocIdBaseValue = LocIdBase
                      { locIdBaseFileVersionId = fileVersionKey
                      , locIdBaseKind = kind
                      , locIdBaseLocId = locId
                      }
                documentKey <- insert documentLocIdBaseValue
                let document = Document
                      { documentDisplayName = displayName
                      , documentName = name
                      , documentLocation = location
                      , documentVersion = version
                      }
                insertEntityMany [Entity (toSqlKey $ fromSqlKey documentKey) document]
                return (True, documentKey, documentLocIdBaseValue)
          let dbCache1 = addDocumentToCache libName documentKey dbCache0
          createAllOmsOfDocument opts libEnv fileVersionKey dbCache1 doSave dGraph
            globalAnnotations libName (Entity documentKey documentLocIdBaseValue)

locIdOfDocument :: HetcatsOpts -> Maybe String -> String -> String
locIdOfDocument opts location displayName =
  let base = fromMaybe displayName location
  in  if null $ libdirs opts
      then base
      else fromMaybe base $ stripPrefix (firstLibdir opts) base

firstLibdir :: HetcatsOpts -> String
firstLibdir opts =
  let libdir' = head $ libdirs opts
  in  if last libdir' == '/' then libdir' else libdir' ++ "/"

-- A FileVersion only exists for the commit that actually changed the file, but
-- the file itself also exists in future commits that changed other files.
-- This function finds the FileVersion of the file at `location` (i.e. the
-- commit that last changed that file).
findFileVersionByPath :: MonadIO m
                      => HetcatsOpts -> Entity FileVersion -> Maybe String
                      -> DBMonad m FileVersionId
findFileVersionByPath opts (Entity fileVersionKey _) location =
  let isInLibdir = not (null $ libdirs opts)
                     && isJust location
                     && head (libdirs opts) `isPrefixOf` fromJust location
      path = fromJust $ stripPrefix (firstLibdir opts) $ fromJust location
      queryString = Text.pack (
        "SELECT file_versions.id "
        ++ "FROM file_versions "
        ++ "INNER JOIN file_version_parents "
        ++ "  ON file_version_parents.last_changed_file_version_id = file_versions.id "
        ++ "INNER JOIN file_versions AS backreference "
        ++ "  ON file_version_parents.queried_sha = backreference.commit_sha "
        ++ "WHERE (file_versions.path = ? "
        ++ "       AND backreference.id = ?);")
  in  if isInLibdir
      then do
            results <-
              rawSql queryString [ toPersistValue path
                                 , toPersistValue fileVersionKey
                                 ]
            if null results
            then return fileVersionKey
            else return $ head results
      else return fileVersionKey

-- Guess the kind of the Document. First, by the filepath only and then, by
-- searching for keywords in the content. If the type cannot be guessed,
-- default to Library.
kindOfDocument :: MonadIO m
               => HetcatsOpts -> Maybe FilePath -> m Enums.LocIdBaseKindType
kindOfDocument opts filepathM = case filepathM of
  Nothing -> return Enums.Library
  Just filepath -> case guess filepath (intype opts) of
    GuessIn -> do
      mimeR <-
        liftIO $ runResultT $ getMagicFileType (Just "--mime-type") filepath
      case maybeResult mimeR of
        Just mime -> return $ determineTypeByMime mime
        Nothing -> return Enums.Library
    t -> return $ determineType t
  where
    determineType :: InType -> Enums.LocIdBaseKindType
    determineType t = if show t `elem` ["casl", "het", "dol"]
                      then Enums.Library
                      else Enums.NativeDocument

    determineTypeByMime :: String -> Enums.LocIdBaseKindType
    determineTypeByMime t = if t `elem` ["text/casl", "text/het", "text/dol"]
                            then Enums.Library
                            else Enums.NativeDocument

createAllOmsOfDocument :: MonadIO m
                       => HetcatsOpts -> LibEnv -> FileVersionId -> DBCache
                       -> Bool -> DGraph -> GlobalAnnos -> LibName
                       -> Entity LocIdBase -> DBMonad m DBCache
createAllOmsOfDocument opts libEnv fileVersionKey dbCache0 doSave dGraph
  globalAnnotations libName documentLocIdBase =
  let labeledNodes = labNodes $ dgBody dGraph
      labeledEdges = labEdges $ dgBody dGraph
  in  do
        dbCache1 <- foldM
          (\ dbCacheAcc labeledNode ->
            fmap (\ (_, _, dbCache) -> dbCache) $
              findOrCreateOMS opts libEnv fileVersionKey dbCacheAcc doSave
                globalAnnotations libName documentLocIdBase labeledNode
          ) dbCache0 labeledNodes
        foldM
          (\ dbCacheAcc labeledEdge ->
            createMapping opts libEnv fileVersionKey dbCacheAcc doSave
              globalAnnotations libName documentLocIdBase labeledEdge
          ) dbCache1 labeledEdges

findOrCreateOMSM :: MonadIO m
                 => HetcatsOpts -> LibEnv -> FileVersionId -> DBCache -> Bool
                 -> GlobalAnnos -> LibName -> Entity LocIdBase -> Maybe Int
                 -> DBMonad m (Maybe LocIdBaseId, Maybe SignatureId, DBCache)
findOrCreateOMSM opts libEnv fileVersionKey dbCache0 doSave globalAnnotations
  libName documentLocIdBase nodeIdM =
  case nodeIdM of
    Nothing -> return (Nothing, Nothing, dbCache0)
    Just nodeId ->
      let nodeLabel = getNodeLabel libEnv libName nodeId
      in  do
            (omsKey, signatureKey, dbCache1) <-
              findOrCreateOMS opts libEnv fileVersionKey dbCache0 doSave
                globalAnnotations libName documentLocIdBase (nodeId, nodeLabel)
            return (Just omsKey, Just signatureKey, dbCache1)

findOrCreateOMS :: MonadIO m
                => HetcatsOpts -> LibEnv -> FileVersionId -> DBCache -> Bool
                -> GlobalAnnos -> LibName -> Entity LocIdBase
                -> (Int, DGNodeLab)
                -> DBMonad m (LocIdBaseId, SignatureId, DBCache)
findOrCreateOMS opts libEnv fileVersionKey dbCache0 doSave globalAnnotations
  libName documentLocIdBase (nodeId, nodeLabel) =
  case cachedOMSKey libName nodeId dbCache0 of
    Just (omsKey, signatureKey) -> return (omsKey, signatureKey, dbCache0)
    Nothing -> case nodeInfo nodeLabel of
      DGRef { ref_node = refNodeId
            , ref_libname = refLibName
            } -> do
        let refNodeLabel = getNodeLabel libEnv refLibName refNodeId
        (omsKey, signatureKey, dbCache1) <-
          findOrCreateOMS opts libEnv fileVersionKey dbCache0 doSave
            globalAnnotations refLibName documentLocIdBase (refNodeId, refNodeLabel)
        return ( omsKey
               , signatureKey
               , addNodeToCache libName nodeId omsKey signatureKey dbCache1
               )
      DGNode _ consStatus -> do
        omsKeyM <- findOMSAndSignature fileVersionKey documentLocIdBase nodeLabel
        case (doSave, omsKeyM) of
          (True, Just (omsKey, signatureKey)) ->
            return ( omsKey
                   , signatureKey
                   , addNodeToCache libName nodeId omsKey signatureKey dbCache0
                   )
          _ ->
            createOMS opts libEnv fileVersionKey dbCache0 doSave
              globalAnnotations libName documentLocIdBase (nodeId, nodeLabel)
              consStatus

createOMS :: MonadIO m
          => HetcatsOpts -> LibEnv -> FileVersionId -> DBCache -> Bool
          -> GlobalAnnos -> LibName -> Entity LocIdBase -> (Int, DGNodeLab)
          -> ConsStatus -> DBMonad m (LocIdBaseId, SignatureId, DBCache)
createOMS opts libEnv fileVersionKey dbCache0 doSave globalAnnotations libName
  documentLocIdBase@(Entity documentKey _) (nodeId, nodeLabel) consStatus =
  let gTheory = dgn_theory nodeLabel
      internalNodeName = dgn_name nodeLabel
      name = show $ getName internalNodeName
      nameExtension = extString internalNodeName
      nameExtensionIndex = extIndex internalNodeName
      displayName = showName internalNodeName
      locId = locIdOfOMS documentLocIdBase nodeLabel
  in  do
        languageKey <- case gTheory of
          G_theory { gTheoryLogic = lid } -> findLanguage lid

        (signatureKey, signatureIsNew, dbCache1) <- case gTheory of
          G_theory { gTheoryLogic = lid
                   , gTheorySignIdx = sigId
                   , gTheorySign = extSign
                   } -> do
           omsKeyM <-
             findOMSAndSignature fileVersionKey documentLocIdBase nodeLabel
           case omsKeyM of
             Just (_, signatureKey) ->
               return ( signatureKey
                      , False
                      , addSignatureToCache libName sigId signatureKey dbCache0
                      )
             Nothing ->
               findOrCreateSignature dbCache0 libName lid extSign sigId
                 languageKey

        (normalFormKeyM, normalFormSignatureKeyM, dbCache2) <-
          findOrCreateOMSM opts libEnv fileVersionKey dbCache1 doSave
            globalAnnotations libName documentLocIdBase $ dgn_nf nodeLabel

        (freeNormalFormKeyM, freeNormalFormSignatureKeyM, dbCache3) <-
          findOrCreateOMSM opts libEnv fileVersionKey dbCache2 doSave
            globalAnnotations libName documentLocIdBase $ dgn_freenf nodeLabel

        (normalFormSignatureMorphismKeyM, _, dbCache4) <-
          findOrCreateSignatureMorphismM opts libEnv dbCache3 doSave libName
            (nodeId, dgn_nf nodeLabel) globalAnnotations
            (signatureKey, normalFormSignatureKeyM) $
            dgn_sigma nodeLabel

        (freeNormalFormSignatureMorphismKeyM, _, dbCache5) <-
          findOrCreateSignatureMorphismM opts libEnv dbCache4 doSave libName
            (nodeId, dgn_freenf nodeLabel) globalAnnotations
            (signatureKey, freeNormalFormSignatureKeyM) $
            dgn_sigma nodeLabel

        omsLocIdBaseEntity@(Entity omsKey _) <-
          if not doSave
          then do
            omsM <- selectFirst [ LocIdBaseLocId ==. locId
                                , LocIdBaseFileVersionId ==. fileVersionKey
                                , LocIdBaseKind ==. Enums.OMS
                                ] []
            case omsM of
              Just entity -> return entity
              Nothing -> fail ("Persistence.DevGraph.createOMS: OMS not found"
                               ++ locId)
          else do
            conservativityStatusKey <- createConservativityStatus consStatus
            nodeNameRangeKey <- createRange $ srcRange internalNodeName

            serializationKey <- case gTheory of
              G_theory { gTheorySyntax = syntaxM } ->
                findOrCreateSerializationM languageKey syntaxM

            logicKey <- case sublogicOfTh gTheory of
              G_sublogics lid sublogics -> findOrCreateLogic' opts lid sublogics

            let omsLocIdBaseValue = LocIdBase
                  { locIdBaseFileVersionId = fileVersionKey
                  , locIdBaseKind = Enums.OMS
                  , locIdBaseLocId = locId
                  }
            omsKey <- insert omsLocIdBaseValue
            let oms = OMS
                  { oMSDocumentId = documentKey
                  , oMSLanguageId = languageKey
                  , oMSLogicId = logicKey
                  , oMSSerializationId = serializationKey
                  , oMSSignatureId = signatureKey
                  , oMSNormalFormId = normalFormKeyM
                  , oMSNormalFormSignatureMorphismId = normalFormSignatureMorphismKeyM
                  , oMSFreeNormalFormId = freeNormalFormKeyM
                  , oMSFreeNormalFormSignatureMorphismId = freeNormalFormSignatureMorphismKeyM
                  , oMSOrigin = omsOrigin
                  , oMSConservativityStatusId = conservativityStatusKey
                  , oMSNameFileRangeId = nodeNameRangeKey
                  , oMSDisplayName = displayName
                  , oMSName = name
                  , oMSNameExtension = nameExtension
                  , oMSNameExtensionIndex = nameExtensionIndex
                  , oMSLabelHasHiding = labelHasHiding nodeLabel
                  , oMSLabelHasFree = labelHasFree nodeLabel
                  }
            insertEntityMany [Entity (toSqlKey $ fromSqlKey omsKey) oms]
            return $ Entity omsKey omsLocIdBaseValue

        dbCache6 <- case gTheory of
          G_theory { gTheoryLogic = lid
                   , gTheorySign = extSign
                   } ->
            createSymbols libEnv fileVersionKey dbCache5 doSave libName nodeId
              omsLocIdBaseEntity lid extSign

        dbCache7 <- case gTheory of
          G_theory { gTheoryLogic = lid
                   , gTheorySign = ExtSign { plainSign = sign }
                   , gTheorySens = sentences
                   } ->
            createSentences libEnv fileVersionKey dbCache6 doSave
              globalAnnotations libName nodeId omsLocIdBaseEntity lid sign
              sentences

        dbCache8 <- case gTheory of
          G_theory { gTheoryLogic = lid
                   , gTheorySign = extSign
                   } ->
            if doSave && signatureIsNew
            then associateSymbolsOfSignature libEnv dbCache7 libName nodeId
                   lid extSign signatureKey
            else return dbCache7

        return ( omsKey
               , signatureKey
               , addNodeToCache libName nodeId omsKey signatureKey dbCache8
               )
  where
    omsOrigin :: OMSOrigin
    omsOrigin = case node_origin $ nodeInfo nodeLabel of
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
      DGVerificationGeneric -> OMSOrigin.DGVerificationGeneric
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


createConservativityStatus :: MonadIO m
                           => ConsStatus -> DBMonad m ConservativityStatusId
createConservativityStatus (ConsStatus r p _) =
  insert SchemaClass.ConservativityStatus
    { conservativityStatusRequired = toString r
    , conservativityStatusProved = toString p
    }
  where
    toString :: Conservativity -> String
    toString c = case c of
      Unknown s -> s
      _ -> map toLower $ show c

findOrCreateSignatureMorphismM :: MonadIO m
                               => HetcatsOpts -> LibEnv -> DBCache -> Bool
                               -> LibName -> (Int, Maybe Int) -> GlobalAnnos
                               -> (SignatureId, Maybe SignatureId)
                               -> Maybe GMorphism
                               -> DBMonad m ( Maybe SignatureMorphismId
                                            , [SymbolMappingId]
                                            , DBCache
                                            )
findOrCreateSignatureMorphismM opts libEnv dbCache doSave libName
  (sourceId, targetIdM) globalAnnotations
  (sourceSignatureKey, targetSignatureKeyM) gMorphismM =
    case gMorphismM of
      Nothing -> return (Nothing, [], dbCache)
      Just gMorphism -> do
        (signatureMorphismKey, symbolMappingKeys, dbCache1) <-
          findOrCreateSignatureMorphism opts libEnv dbCache doSave libName
            (sourceId, fromJust targetIdM) globalAnnotations
            (sourceSignatureKey, fromJust targetSignatureKeyM) gMorphism
        return (Just signatureMorphismKey, symbolMappingKeys, dbCache1)

findOrCreateSignatureMorphism :: MonadIO m
                              => HetcatsOpts -> LibEnv -> DBCache -> Bool
                              -> LibName -> (Int, Int) -> GlobalAnnos
                              -> (SignatureId, SignatureId)
                              -> GMorphism
                              -> DBMonad m ( SignatureMorphismId
                                           , [SymbolMappingId]
                                           , DBCache
                                           )
findOrCreateSignatureMorphism opts libEnv dbCache doSave libName edge
  globalAnnotations (sourceSignatureKey, targetSignatureKey) gMorphism =
    case gMorphism of
      GMorphism { gMorphismComor = cid
                , gMorphismMorIdx = morphismId
                } ->
        case Map.lookup (libName, morphismId) $ signatureMorphismMap dbCache of
          Just (signatureMorphismKey, symbolMappingKeys, _) ->
            return (signatureMorphismKey, symbolMappingKeys, dbCache)
          Nothing ->
            let json = ppJson $ ToJson.gmorph opts globalAnnotations gMorphism
            in do
                (_, logicMappingKey) <-
                  findOrCreateLanguageMappingAndLogicMapping opts $ Comorphism cid
                signatureMorphismKey <-
                  if doSave
                  then insert SignatureMorphism
                        { signatureMorphismLogicMappingId = logicMappingKey
                        , signatureMorphismAsJson = json
                        , signatureMorphismSourceId = sourceSignatureKey
                        , signatureMorphismTargetId = targetSignatureKey
                        }
                  else do
                    signatureMorphismM <-
                      selectFirst [ SignatureMorphismLogicMappingId ==. logicMappingKey
                                  , SignatureMorphismSourceId ==. sourceSignatureKey
                                  , SignatureMorphismTargetId ==. targetSignatureKey
                                  , SignatureMorphismAsJson ==. json
                                  ] []
                    case signatureMorphismM of
                      Nothing -> fail "Persistence.DevGraph.findOrCreateSignatureMorphism: not found "
                      Just (Entity key _) -> return key

                (symbolMappingKeys, dbCache1) <-
                  findOrCreateSymbolMappings libEnv dbCache doSave libName edge
                    signatureMorphismKey gMorphism

                let signatureMorphismMap' =
                      Map.insert (libName, morphismId)
                        (signatureMorphismKey, symbolMappingKeys, gMorphism) $
                        signatureMorphismMap dbCache1
                let dbCache2 =
                      dbCache1 { signatureMorphismMap = signatureMorphismMap' }
                return ( signatureMorphismKey
                       , symbolMappingKeys
                       , dbCache2
                       )

findOrCreateSymbolMappings :: MonadIO m
                           => LibEnv -> DBCache -> Bool -> LibName -> (Int, Int)
                           -> SignatureMorphismId -> GMorphism
                           -> DBMonad m ([SymbolMappingId], DBCache)
findOrCreateSymbolMappings libEnv dbCache doSave libName edge
  signatureMorphismKey gMorphism = case gMorphism of
    GMorphism { gMorphismComor = cid
              , gMorphismMor = morphism
              , gMorphismSign = extSign@ExtSign { plainSign = sign }
              } ->
      let sourceLid = sourceLogic cid
          targetLid = targetLogic cid
          symbolMap = symmap_of targetLid morphism
      in  do
            symbolMappingKeys <-
              concatMapM
                (\ sourceSymbol ->
                  concatMapM
                    (\ translatedSymbol ->
                      case Map.lookup translatedSymbol symbolMap of
                        Nothing -> return []
                        Just targetSymbol -> do
                            symbolMappingKey <-
                              findOrCreateSymbolMapping libEnv dbCache doSave
                                libName edge signatureMorphismKey sourceLid
                                targetLid sourceSymbol targetSymbol
                            return [symbolMappingKey]
                    ) $ Set.toList $ map_symbol cid sign sourceSymbol
                ) $ Set.toList $ symset_of sourceLid $ plainSign extSign
            return (symbolMappingKeys, dbCache)

findOrCreateSymbolMapping :: ( MonadIO m
                             , Sentences lid1 sentence1 sign1 morphism1 symbol1
                             , Sentences lid2 sentence2 sign2 morphism2 symbol2
                             )
                          => LibEnv -> DBCache -> Bool -> LibName -> (Int, Int)
                          -> SignatureMorphismId
                          -> lid1 -> lid2 -> symbol1 -> symbol2
                          -> DBMonad m SymbolMappingId
findOrCreateSymbolMapping libEnv dbCache doSave libName (sourceId, targetId)
  signatureMorphismKey sourceLid targetLid sourceSymbol targetSymbol = do
  sourceKey <-
    fromJustFail (symbolErrorMessage libEnv libName sourceId sourceSymbol sourceLid "source") $
      findSymbolInCache libEnv libName sourceId sourceLid sourceSymbol dbCache

  targetKey <-
    fromJustFail (symbolErrorMessage libEnv libName targetId targetSymbol targetLid "target") $
      findSymbolInCache libEnv libName targetId targetLid targetSymbol dbCache

  symbolMappingM <-
    selectFirst [ SymbolMappingSignatureMorphismId ==. signatureMorphismKey
                , SymbolMappingSourceId ==. sourceKey
                , SymbolMappingTargetId ==. targetKey
                ] []
  case symbolMappingM of
    Just (Entity symbolMappingKey _) -> return symbolMappingKey
    Nothing ->
      if doSave
      then insert SymbolMapping
            { symbolMappingSignatureMorphismId = signatureMorphismKey
            , symbolMappingSourceId = sourceKey
            , symbolMappingTargetId = targetKey
            }
      else fail "Persistence.DevGraph.findOrCreateSymbolMapping: not found"

symbolErrorMessage :: Sentences lid sentence sign morphism symbol
                   => LibEnv -> LibName -> Node -> symbol -> lid -> String
                   -> String
symbolErrorMessage libEnv libName nodeId symbol lid end =
  let (libNameDereferenced, nodeIdDereferenced) = dereferenceNodeId libEnv libName nodeId
      fullName = show $ fullSymName lid symbol
      symbolKind = symKind lid symbol
      nodeName = show $ getName $ dgn_name $ getNodeLabel libEnv libName nodeId
  in  "Could not find " ++ end ++ " symbol for SymbolMapping:"
      ++ "\nsymbol name: " ++ fullName
      ++ "\nsymbol kind: " ++ symbolKind
      ++ "\nnode name: " ++ nodeName
      ++ "\nnode ID: " ++ show nodeIdDereferenced
      ++ "\nlibrary name: " ++ show libNameDereferenced
      ++ "\nThis is a system error. Please report it at https://github.com/spechub/Hets/issues"


findOrCreateSerializationM :: MonadIO m
                           => LanguageId -> Maybe IRI
                           -> DBMonad m (Maybe SerializationId)
findOrCreateSerializationM languageKey syntaxM =
  case syntaxM of
    Nothing -> return Nothing
    Just syntaxIRI -> do
      let syntaxIRIString = show $ setAngles False syntaxIRI
      serializationM <- selectFirst [SerializationName ==. syntaxIRIString] []
      case serializationM of
        Just (Entity serializationKey _) -> return $ Just serializationKey
        Nothing -> do
          serializationKey <- insert Serialization
            { serializationLanguageId = languageKey
            , serializationSlug = parameterize syntaxIRIString
            , serializationName = syntaxIRIString
            }
          return $ Just serializationKey

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

findOrCreateLogic' :: ( MonadIO m
                      , Logic.Logic lid sublogics
                          basic_spec sentence symb_items symb_map_items
                          sign morphism symbol raw_symbol proof_tree
                      )
                   => HetcatsOpts -> lid -> sublogics -> DBMonad m LogicId
findOrCreateLogic' opts lid sublogic = do
  languageKey <- findLanguage lid
  findOrCreateLogic opts languageKey lid sublogic

findOrCreateSignature :: ( MonadIO m
                         , Sentences lid sentence sign morphism symbol
                         )
                      => DBCache -> LibName -> lid -> ExtSign sign symbol
                      -> SigId -> LanguageId
                      -> DBMonad m (SignatureId, Bool, DBCache)
findOrCreateSignature dbCache libName lid extSign sigId languageKey =
  case Map.lookup (libName, sigId) $ signatureMap dbCache of
    Just signatureKey -> return (signatureKey, False, dbCache)
    Nothing -> do
      signatureKey <- insert Signature
        { signatureLanguageId = languageKey
        , signatureAsJson = ppJson $ ToJson.symbols lid extSign
        }
      return ( signatureKey
             , True
             , addSignatureToCache libName sigId signatureKey dbCache
             )

createSymbols :: ( MonadIO m
                 , Sentences lid sentence sign morphism symbol
                 )
              => LibEnv -> FileVersionId -> DBCache -> Bool -> LibName -> Int
              -> Entity LocIdBase -> lid -> ExtSign sign symbol
              -> DBMonad m DBCache
createSymbols libEnv fileVersionKey dbCache doSave libName nodeId omsLocIdBase
  lid ExtSign { plainSign = sign } =
  foldM (\ dbCacheAcc symbol ->
          findOrCreateSymbol libEnv fileVersionKey dbCacheAcc doSave libName
            nodeId omsLocIdBase lid symbol
        ) dbCache $ symlist_of lid sign

findOrCreateSymbol :: ( MonadIO m
                      , Sentences lid sentence sign morphism symbol
                      )
                   => LibEnv -> FileVersionId -> DBCache -> Bool -> LibName
                   -> Int -> Entity LocIdBase -> lid -> symbol
                   -> DBMonad m DBCache
findOrCreateSymbol libEnv fileVersionKey dbCache doSave libName nodeId
  (Entity omsKey omsLocIdBaseValue) lid symbol =
    let name = show $ sym_name lid symbol
        fullName = fullSymName lid symbol
        symbolKind = symKind lid symbol
        locId = locIdBaseLocId omsLocIdBaseValue ++ "/symbols/" ++ symbolKind ++ "/" ++ name
    in  if symbolIsCached libEnv libName nodeId lid symbol dbCache
        then return dbCache
        else do
          symbolKey <-
            if doSave
            then do
              symbolKey <- insert LocIdBase
                { locIdBaseFileVersionId = fileVersionKey
                , locIdBaseKind = Enums.Symbol
                , locIdBaseLocId = locId
                }
              let symbolValue = Symbol
                    { symbolOmsId = omsKey
                    , symbolFileRangeId = Nothing
                    , symbolSymbolKind = symbolKind
                    , symbolName = name
                    , symbolFullName = Text.pack fullName
                    }
              insertEntityMany [Entity (toSqlKey $ fromSqlKey symbolKey) symbolValue]
              return symbolKey
            else do
              symbolM <- selectFirst [ LocIdBaseLocId ==. locId
                                     , LocIdBaseFileVersionId ==. fileVersionKey
                                     , LocIdBaseKind ==. Enums.Symbol
                                     ] []
              case symbolM of
                Nothing -> fail ("Persistence.DevGraph.findOrCreateSymbol: "
                                 ++ "Symbol not found: " ++ locId)
                Just (Entity symbolKey _) -> return symbolKey
          return $ addSymbolToCache libEnv libName nodeId lid symbol symbolKey dbCache

createSentences :: ( MonadIO m
                   , GetRange sentence
                   , Pretty sentence
                   , Sentences lid sentence sign morphism symbol
                   )
                => LibEnv -> FileVersionId -> DBCache -> Bool -> GlobalAnnos
                -> LibName -> Int -> Entity LocIdBase -> lid -> sign
                -> ThSens sentence (AnyComorphism, BasicProof)
                -> DBMonad m DBCache
createSentences libEnv fileVersionKey dbCache0 doSave globalAnnotations libName
  nodeId omsLocId lid sign sentences =
  let (axioms, conjectures) = OMap.partition isAxiom sentences
      namedAxioms = toNamedList axioms
      orderedConjectures = OMap.toList conjectures
  in do
    dbCache1 <- createAxioms libEnv fileVersionKey dbCache0 doSave
      globalAnnotations libName nodeId omsLocId lid sign namedAxioms
    createConjectures libEnv fileVersionKey dbCache1 doSave
      globalAnnotations libName nodeId omsLocId lid sign orderedConjectures

createAxioms :: ( MonadIO m
                , Foldable t
                , Sentences lid sentence sign morphism symbol
                )
             => LibEnv -> FileVersionId -> DBCache -> Bool -> GlobalAnnos
             -> LibName -> Int -> Entity LocIdBase -> lid -> sign
             -> t (Named sentence)
             -> DBMonad m DBCache
createAxioms libEnv fileVersionKey dbCache doSave globalAnnotations libName
  nodeId omsLocId lid sign =
  foldM (\ dbCacheAcc namedAxiom -> do
          (axiomKey, dbCacheAcc1) <-
            createSentence fileVersionKey dbCacheAcc doSave globalAnnotations
              omsLocId lid sign False False namedAxiom
          associateSymbolsOfSentence libEnv fileVersionKey dbCacheAcc1 doSave
            libName nodeId omsLocId axiomKey lid sign namedAxiom
        ) dbCache

createConjectures :: ( MonadIO m
                     , Foldable t
                     , Sentences lid sentence sign morphism symbol
                     )
                  => LibEnv -> FileVersionId -> DBCache -> Bool -> GlobalAnnos
                  -> LibName -> Int -> Entity LocIdBase -> lid -> sign
                  -> t (String, SenStatus sentence (AnyComorphism, BasicProof))
                  -> DBMonad m DBCache
createConjectures libEnv fileVersionKey dbCache doSave globalAnnotations libName
  nodeId omsLocId lid sign =
  foldM (\ dbCacheAcc (name, senStatus) ->
          let namedConjecture = toNamed name senStatus
              isProved = isProvenSenStatus senStatus
          in do
            (conjectureKey, dbCacheAcc1) <-
              createSentence fileVersionKey dbCacheAcc doSave globalAnnotations
                omsLocId lid sign True isProved namedConjecture
            associateSymbolsOfSentence libEnv fileVersionKey dbCacheAcc1 doSave
              libName nodeId omsLocId conjectureKey lid sign namedConjecture
        ) dbCache

createSentence :: ( MonadIO m
                  , GetRange sentence
                  , Pretty sentence
                  , Sentences lid sentence sign morphism symbol
                  )
               => FileVersionId -> DBCache -> Bool -> GlobalAnnos
               -> Entity LocIdBase -> lid -> sign -> Bool -> Bool
               -> Named sentence -> DBMonad m (LocIdBaseId, DBCache)
createSentence fileVersionKey dbCache doSave globalAnnotations
  (Entity omsKey omsLocIdBaseValue) lid sign isConjecture isProved namedSentence =
  let name = senAttr namedSentence
      range = getRangeSpan $ sentence namedSentence
      locId = locIdBaseLocId omsLocIdBaseValue ++ "/sentences/" ++ name
      text = show $ useGlobalAnnos globalAnnotations $
               print_named lid $ makeNamed "" $
               simplify_sen lid sign $ sentence namedSentence
      kind =
        if isConjecture
        then if isProved
             then Enums.Theorem
             else Enums.OpenConjecture
        else Enums.Axiom
      evaluationState =
        if isProved
        then EvaluationStateType.FinishedSuccessfully
        else EvaluationStateType.NotYetEnqueued
      reasoningStatus =
        if isProved
        then ReasoningStatusOnConjectureType.THM
        else ReasoningStatusOnConjectureType.OPN
  in  do
        sentenceKey <-
          if doSave
          then do
               rangeKeyM <- createRange range
               sentenceKey <- insert LocIdBase
                 { locIdBaseFileVersionId = fileVersionKey
                 , locIdBaseKind = kind
                 , locIdBaseLocId = locId
                 }
               let sentenceValue = Sentence
                     { sentenceOmsId = omsKey
                     , sentenceFileRangeId = rangeKeyM
                     , sentenceName = name
                     , sentenceText = Text.pack text
                     }
               insertEntityMany [Entity (toSqlKey $ fromSqlKey sentenceKey) sentenceValue]
               if isConjecture
               then let conjecture = Conjecture
                          { conjectureEvaluationState = evaluationState
                          , conjectureReasoningStatus = reasoningStatus
                          }
                    in  insertEntityMany [Entity (toSqlKey $ fromSqlKey sentenceKey) conjecture]
               else let axiom = Axiom { }
                    in insertEntityMany [Entity (toSqlKey $ fromSqlKey sentenceKey) axiom]
               return sentenceKey
            else do
              sentenceM <- selectFirst [ LocIdBaseLocId ==. locId
                                       , LocIdBaseFileVersionId ==. fileVersionKey
                                       , LocIdBaseKind ==. kind
                                       ] []
              case sentenceM of
                Nothing -> fail ("Persistence.DevGraph.createSentence: Sentence not found"
                                 ++ locId)
                Just (Entity sentenceKey _) -> return sentenceKey
        return (sentenceKey, dbCache)

associateSymbolsOfSentence :: ( MonadIO m
                              , GetRange sentence
                              , Pretty sentence
                              , Sentences lid sentence sign morphism symbol
                              )
                           => LibEnv -> FileVersionId -> DBCache -> Bool
                           -> LibName -> Int -> Entity LocIdBase -> LocIdBaseId
                           -> lid -> sign -> Named sentence
                           -> DBMonad m DBCache
associateSymbolsOfSentence libEnv fileVersionKey dbCache doSave libName nodeId
  omsLocIdBase sentenceKey lid sign namedSentence =
  let symbolsOfSentence = symsOfSen lid sign $ sentence namedSentence
  in  do
        (dbCache', _) <-
          foldM (\ (dbCacheAcc, associatedSymbols) symbol ->
                  let mapIndex = symbolMapIndex lid symbol
                  in  if Set.member mapIndex associatedSymbols
                      then return (dbCacheAcc, associatedSymbols)
                      else case findSymbolInCache libEnv libName nodeId lid symbol dbCacheAcc of
                             Just symbolKey -> do
                               when doSave $
                                 insert SentenceSymbol
                                   { sentenceSymbolSentenceId = sentenceKey
                                   , sentenceSymbolSymbolId = symbolKey
                                   } >> return ()
                               return ( dbCacheAcc
                                      , Set.insert mapIndex associatedSymbols
                                      )
                             Nothing -> do
                               dbCacheAcc' <-
                                 findOrCreateSymbol libEnv fileVersionKey
                                   dbCacheAcc doSave libName nodeId omsLocIdBase
                                   lid symbol
                               return ( dbCacheAcc'
                                      , Set.insert mapIndex associatedSymbols
                                      )
                ) (dbCache, Set.empty) symbolsOfSentence
        return dbCache'

associateSymbolsOfSignature :: ( MonadIO m
                               , Sentences lid sentence sign morphism symbol
                               )
                            => LibEnv -> DBCache -> LibName -> Int -> lid
                            -> ExtSign sign symbol -> SignatureId
                            -> DBMonad m DBCache
associateSymbolsOfSignature libEnv dbCache libName nodeId lid extSign signatureKey =
  let ownSymbols = nonImportedSymbols extSign
      allSymbols = symset_of lid $ plainSign extSign
  in do
       foldM_
         (\ associatedSymbols symbol ->
           let mapIndex = symbolMapIndex lid symbol
               symbolKey =
                 fromJust $ findSymbolInCache libEnv libName nodeId lid symbol
                   dbCache
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

createMapping :: MonadIO m
              => HetcatsOpts -> LibEnv -> FileVersionId -> DBCache -> Bool
              -> GlobalAnnos -> LibName -> Entity LocIdBase
              -> (Int, Int, DGLinkLab) -> DBMonad m DBCache
createMapping opts libEnv fileVersionKey dbCache doSave globalAnnotations
  libName documentLocIdBase@(Entity _ documentLocIdBaseValue)
  (sourceId, targetId, linkLabel) = do
  (sourceOMSKey, sourceSignatureKey) <-
    case Map.lookup (libName, sourceId) $ nodeMap dbCache of
      Just (omsKey, signatureKey) -> return (omsKey, signatureKey)
      Nothing -> fail ("Persistence.DevGraph.createMapping: Could not find source node with ID " ++ show (libName, sourceId))

  (targetOMSKey, targetSignatureKey) <-
    case Map.lookup (libName, targetId) $ nodeMap dbCache of
      Just (omsKey, signatureKey) -> return (omsKey, signatureKey)
      Nothing -> fail ("Persistence.DevGraph.createMapping: Could not find target node with ID " ++ show (libName, targetId))

  (signatureMorphismKey, _, dbCache1) <-
    findOrCreateSignatureMorphism opts libEnv dbCache True libName
      (sourceId, targetId) globalAnnotations
      (sourceSignatureKey, targetSignatureKey) $ dgl_morphism linkLabel

  let displayName = if null $ dglName linkLabel
                    then show (dgl_id linkLabel)
                    else dglName linkLabel
  let locId = locIdBaseLocId documentLocIdBaseValue ++ "//mappings/" ++ displayName
  mappingM <- selectFirst [ LocIdBaseFileVersionId ==. fileVersionKey
                          , LocIdBaseKind ==. Enums.Mapping
                          , LocIdBaseLocId ==. locId
                          ] []
  if isJust mappingM
  then return dbCache1
  else do
    conservativityStatusKeyM <- case dgl_type linkLabel of
      ScopedLink _ _ consStatus ->
        fmap Just $ createConservativityStatus consStatus
      _ -> return Nothing

    (freenessParameterOMSKeyM, dbCache2) <- case dgl_type linkLabel of
      FreeOrCofreeDefLink _ (JustNode NodeSig { getNode = nodeId }) -> do
        let nodeLabel = getNodeLabel libEnv libName nodeId
        (freenessParameterOMSKey, _, dbCache') <-
          findOrCreateOMS opts libEnv fileVersionKey dbCache1 doSave
            globalAnnotations libName documentLocIdBase (nodeId, nodeLabel)
        return (Just freenessParameterOMSKey, dbCache')
      _ -> return (Nothing, dbCache)

    freenessParameterLanguageKeyM <- case dgl_type linkLabel of
      FreeOrCofreeDefLink _ (EmptyNode (Logic.Logic lid)) ->
        fmap Just $ findLanguage lid
      _ -> return Nothing

    mappingKey <- insert LocIdBase
      { locIdBaseFileVersionId = fileVersionKey
      , locIdBaseKind = Enums.Mapping
      , locIdBaseLocId = locId
      }
    let mapping = Mapping
          { mappingSourceId = sourceOMSKey
          , mappingTargetId = targetOMSKey
          , mappingSignatureMorphismId = signatureMorphismKey
          , mappingConservativityStatusId = conservativityStatusKeyM
          , mappingFreenessParameterOMSId = freenessParameterOMSKeyM
          , mappingFreenessParameterLanguageId = freenessParameterLanguageKeyM
          , mappingDisplayName = displayName
          , mappingName = dglName linkLabel
          , mappingType = mappingTypeOfLinkLabel
          , mappingOrigin = mappingOriginOfLinkLabel
          , mappingPending = dglPending linkLabel
          }
    insertEntityMany [Entity (toSqlKey $ fromSqlKey mappingKey) mapping]
    return dbCache2
  where
    mappingOriginOfLinkLabel :: MappingOrigin
    mappingOriginOfLinkLabel = case dgl_origin linkLabel of
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

    mappingTypeOfLinkLabel :: MappingType
    mappingTypeOfLinkLabel = case dgl_type linkLabel of
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


cachedOMSKey :: LibName -> Int -> DBCache -> Maybe (LocIdBaseId, SignatureId)
cachedOMSKey libName nodeId = Map.lookup (libName, nodeId) . nodeMap

symbolIsCached :: Sentences lid sentence sign morphism symbol
               => LibEnv -> LibName -> Int -> lid -> symbol -> DBCache -> Bool
symbolIsCached libEnv libName nodeId lid symbol =
  isJust . findSymbolInCache libEnv libName nodeId lid symbol

-- Gives the node label to an id. Use only if the combination exists.
getNodeLabel :: LibEnv -> LibName -> Int -> DGNodeLab
getNodeLabel libEnv libName nodeId =
  fromJust $ fmap Graph.nodeLabel $ IntMap.lookup nodeId $ convertToMap $
    dgBody $ fromJust $ Map.lookup libName libEnv

dereferenceNodeId :: LibEnv -> LibName -> Int -> (LibName, Int)
dereferenceNodeId libEnv libName nodeId =
  case nodeInfo $ getNodeLabel libEnv libName nodeId of
    DGNode {} -> (libName, nodeId)
    DGRef { ref_node = refNodeId
          , ref_libname = refLibName
          } -> dereferenceNodeId libEnv refLibName refNodeId

addDocumentToCache :: LibName -> LocIdBaseId -> DBCache -> DBCache
addDocumentToCache libName documentKey dbCache =
  dbCache { documentMap = Map.insert libName documentKey $ documentMap dbCache }

addNodeToCache :: LibName -> Int -> LocIdBaseId -> SignatureId -> DBCache
               -> DBCache
addNodeToCache libName nodeId omsKey signatureKey dbCache =
  dbCache { nodeMap = Map.insert (libName, nodeId) (omsKey, signatureKey) $
                        nodeMap dbCache
          }

addSignatureToCache :: LibName -> SigId -> SignatureId -> DBCache -> DBCache
addSignatureToCache libName sigId signatureKey dbCache =
  dbCache { signatureMap = Map.insert (libName, sigId) signatureKey $
                             signatureMap dbCache }

addSymbolToCache :: Sentences lid sentence sign morphism symbol
                 => LibEnv -> LibName -> Int -> lid -> symbol -> LocIdBaseId
                 -> DBCache -> DBCache
addSymbolToCache libEnv libName nodeId lid symbol symbolKey dbCache =
  let mapIndex = symbolMapIndex lid symbol
      (libNameDereferenced, nodeIdDereferenced) = dereferenceNodeId libEnv libName nodeId
  in  dbCache { symbolKeyMap =
                  Map.insert (libNameDereferenced, nodeIdDereferenced, mapIndex) symbolKey $
                    symbolKeyMap dbCache
              }

findSymbolInCache :: Sentences lid sentence sign morphism symbol
                  => LibEnv -> LibName -> Int -> lid -> symbol
                  -> DBCache -> Maybe LocIdBaseId
findSymbolInCache libEnv libName nodeId lid symbol dbCache =
  let mapIndex = symbolMapIndex lid symbol
      (libNameDereferenced, nodeIdDereferenced) = dereferenceNodeId libEnv libName nodeId
  in  Map.lookup (libNameDereferenced, nodeIdDereferenced, mapIndex) $ symbolKeyMap dbCache

findOMSAndSignature :: MonadIO m
                    => FileVersionId -> Entity LocIdBase -> DGNodeLab
                    -> DBMonad m (Maybe (LocIdBaseId, SignatureId))
findOMSAndSignature fileVersionKey documentLocIdBase nodeLabel = do
  omsLocIdM <- selectFirst [ LocIdBaseFileVersionId ==. fileVersionKey
                           , LocIdBaseKind ==. Enums.OMS
                           , LocIdBaseLocId ==. locIdOfOMS documentLocIdBase nodeLabel
                           ] []
  case omsLocIdM of
    Just (Entity omsKey _) -> do
      omsValueM <- selectFirst [OMSId ==. toSqlKey (fromSqlKey omsKey)] []
      omsValue <- case omsValueM of
        Nothing ->
          fail ("Persistence.DevGraph.findOMSAndSignature could not find OMS with ID "
                ++ show (unSqlBackendKey $ unLocIdBaseKey omsKey))
        Just (Entity _ omsValue) -> return omsValue
      return $ Just (omsKey, oMSSignatureId omsValue)
    Nothing -> return Nothing

locIdOfOMS :: Entity LocIdBase -> DGNodeLab -> String
locIdOfOMS (Entity _ documentLocIdBaseValue) nodeLabel =
  case locIdBaseKind documentLocIdBaseValue of
    Enums.NativeDocument -> showName $ dgn_name nodeLabel
    _ -> locIdBaseLocId documentLocIdBaseValue
         ++ "//oms/" ++ showName (dgn_name nodeLabel)

symbolMapIndex :: Sentences lid sentence sign morphism symbol
               => lid -> symbol -> SymbolMapIndex
symbolMapIndex lid symbol =
  let fullName = show $ fullSymName lid symbol
      symbolKind = symKind lid symbol
  in (symbolKind, fullName)




createDocumentLinks :: MonadIO m
                    => DBCache -> Rel LibName
                    -> DBMonad m ()
createDocumentLinks dbCache dependencyLibNameRel =
  mapM_ (\ (targetLibName, sourceLibNamesSet) ->
          mapM_ (createDocumentLink targetLibName) $
            Set.toList sourceLibNamesSet
        ) $ Map.toList $ Rel.toMap dependencyLibNameRel
  where
    createDocumentLink :: MonadIO m
                       => LibName -> LibName -> DBMonad m ()
    createDocumentLink sourceLibName targetLibName = do
      -- These libNames must be in the documentMap by construction
      let sourceKey = fromJust $ Map.lookup sourceLibName $ documentMap dbCache
      let targetKey = fromJust $ Map.lookup targetLibName $ documentMap dbCache
      insert DocumentLink { documentLinkSourceId = sourceKey
                          , documentLinkTargetId = targetKey
                          }
      return ()


fromJustFail :: MonadIO m => String -> Maybe a -> m a
fromJustFail message maybeValue = case maybeValue of
  Just value -> return value
  Nothing -> fail message
