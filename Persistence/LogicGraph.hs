{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}
module Persistence.LogicGraph ( migrateLogicGraphKey
                              , exportLogicGraph
                              , findOrCreateLogic
                              , findOrCreateLanguageMappingAndLogicMapping
                              , findReasoner
                              , findOrCreateProver
                              , findOrCreateConsistencyChecker
                              , findLogicMappingByComorphism
                              , findOrCreateLogicTranslation
                              , findReasonerByProverOrConsChecker
                              , findReasonerByGConsChecker
                              , findReasonerByGProver
                              ) where

import Persistence.Database
import Persistence.Schema as DatabaseSchema
import Persistence.Utils
import qualified Persistence.Schema.Enums as Enums

import qualified Comorphisms.LogicGraph as LogicGraph (logicGraph)
import Common.Utils (splitByList)
import Driver.Options
import Driver.Version
import Logic.Grothendieck
import Logic.Logic as Logic
import Logic.Comorphism as Comorphism
import Proofs.AbstractState (ProverOrConsChecker (..), G_prover (..), G_cons_checker (..), getProverName, getCcName)

import Control.Monad (unless)
import Control.Monad.IO.Class (MonadIO (..))
import Data.List (isPrefixOf)
import Database.Persist hiding ((==.))
import Database.Esqueleto

migrateLogicGraphKey :: String
migrateLogicGraphKey = "migrateLogicGraph"

exportLogicGraph :: HetcatsOpts -> IO ()
exportLogicGraph opts =
  onDatabase (databaseConfig opts) $
    advisoryLocked opts migrateLogicGraphKey $ migrateLogicGraph opts

migrateLogicGraph :: MonadIO m => HetcatsOpts -> DBMonad m ()
migrateLogicGraph opts = do
  let versionKeyName = "lastMigratedVersion"
  do
    lastMigratedVersionL <- select $ from $ \hets -> do
      where_ (hets ^. HetsKey ==. val versionKeyName)
      return hets
    case lastMigratedVersionL of
      [] ->
        insert (Hets versionKeyName hetsVersionNumeric) >> migrateLogicGraph' opts
      Entity _ value : _ ->
        unless (hetsValue value == hetsVersionNumeric) $ migrateLogicGraph' opts

migrateLogicGraph' :: MonadIO m => HetcatsOpts -> DBMonad m ()
migrateLogicGraph' opts = do
  exportLanguagesAndLogics opts LogicGraph.logicGraph
  exportLanguageMappingsAndLogicMappings opts LogicGraph.logicGraph
  exportReasoners opts LogicGraph.logicGraph

-- Export all Languages and Logics. Add those that have been added since a
-- previous version of Hets. This does not delete Languages or Logics.
exportLanguagesAndLogics :: MonadIO m
                         => HetcatsOpts -> LogicGraph -> DBMonad m ()
exportLanguagesAndLogics opts logicGraph =
  mapM_ (\ (Logic.Logic lid) -> do
          languageKey <- findOrCreateLanguage lid
          mapM_ (findOrCreateLogic opts languageKey lid) $ all_sublogics lid
        ) $ logics logicGraph

findOrCreateLanguage :: ( MonadIO m
                        , Logic.Logic lid sublogics basic_spec sentence
                            symb_items symb_map_items sign morphism symbol
                            raw_symbol proof_tree
                        )
                     => lid -> DBMonad m LanguageId
findOrCreateLanguage lid = do
  let languageSlugS = slugOfLanguageByName $ language_name lid
  languageM <- findLanguage languageSlugS
  case languageM of
    Nothing -> insert Language
        { languageSlug = languageSlugS
        , languageName = show lid
        , languageDescription = description lid
        , languageStandardizationStatus = "TODO" -- TODO: add to class Logic
        , languageDefinedBy = "registry" -- TODO: add to class Logic (URL)
        }
    Just (Entity key _) -> return key

findLanguage :: MonadIO m
             => String -> DBMonad m (Maybe (Entity DatabaseSchema.Language))
findLanguage languageSlugS = do
  languageL <- select $ from $ \languages -> do
    where_ (languages ^. LanguageSlug ==. val languageSlugS)
    return languages
  case languageL of
    [] -> return Nothing
    entity : _ -> return $ Just entity


findOrCreateLogic :: ( MonadIO m
                     , Logic.Logic lid sublogics basic_spec sentence
                         symb_items symb_map_items sign morphism symbol
                         raw_symbol proof_tree
                     )
                  => HetcatsOpts -> LanguageId -> lid -> sublogics
                  -> DBMonad m LogicId
findOrCreateLogic opts languageKey lid sublogic = do
  let logicNameS = logicNameForDB lid sublogic
  let logicSlugS = slugOfLogicByName logicNameS
  logicM <- findLogic logicSlugS
  case logicM of
    Nothing ->
      -- This is a two-staged process to save some performance:
      -- Case 1: If the logic existed beforehand, then we don't lock the
      -- database and return the logic ID. This is expected to happen very
      -- frequently.
      -- Case 2: If the logic did not exist at this point, we need to create
      -- it atomically. To do this, we do a find-or-create pattern inside a
      -- mutex. This is expected to happen only a few times.
      advisoryLocked opts migrateLogicGraphKey $ do
        logicM' <- findLogic logicSlugS
        case logicM' of
          Nothing -> insert DatabaseSchema.Logic
            { logicLanguageId = languageKey
            , logicSlug = logicSlugS
            , logicName = logicNameS
            }
          Just (Entity key _) -> return key
    Just (Entity key _) -> return key

findLogic :: MonadIO m
          => String -> DBMonad m (Maybe (Entity DatabaseSchema.Logic))
findLogic logicSlugS = do
  logicL <- select $ from $ \logicsSql -> do
    where_ (logicsSql ^. LogicSlug ==. val logicSlugS)
    return logicsSql
  case logicL of
    [] -> return Nothing
    entity : _ -> return $ Just entity

-- Export all LanguageMappings and LogicMappings. Add those that have been added
-- since a previous version of Hets. This does not delete any of the old
-- mappings.
exportLanguageMappingsAndLogicMappings :: MonadIO m
                                       => HetcatsOpts
                                       -> LogicGraph -> DBMonad m ()
exportLanguageMappingsAndLogicMappings opts logicGraph =
  mapM_ (findOrCreateLanguageMappingAndLogicMapping opts) $
    comorphisms logicGraph

findOrCreateLanguageMappingAndLogicMapping :: MonadIO m
                                           => HetcatsOpts -> AnyComorphism
                                           -> DBMonad m ( LanguageMappingId
                                                        , LogicMappingId
                                                        )
findOrCreateLanguageMappingAndLogicMapping opts (Comorphism.Comorphism cid) =
  let sourceLanguageSlugS = slugOfLanguageByName $ language_name $ sourceLogic cid
      targetLanguageSlugS = slugOfLanguageByName $ language_name $ targetLogic cid
  in do
    -- Find the IDs in the databases:
    Entity sourceLanguageKey _ : _ <- select $ from $ \languages -> do
      where_ (languages ^. LanguageSlug ==. val sourceLanguageSlugS)
      return languages

    Entity targetLanguageKey _ : _ <- select $ from $ \languages -> do
      where_ (languages ^. LanguageSlug ==. val targetLanguageSlugS)
      return languages

    sourceLogicKey <-
      findOrCreateLogic opts sourceLanguageKey (sourceLogic cid) $ sourceSublogic cid
    targetLogicKey <-
      findOrCreateLogic opts targetLanguageKey (targetLogic cid) $ targetSublogic cid

    languageMappingKey <-
      findOrCreateLanguageMapping sourceLanguageKey targetLanguageKey
    logicMappingKey <-
      findOrCreateLogicMapping sourceLogicKey targetLogicKey languageMappingKey $ Comorphism.Comorphism cid

    return (languageMappingKey, logicMappingKey)

findOrCreateLanguageMapping :: MonadIO m
                            => LanguageId -> LanguageId
                            -> DBMonad m LanguageMappingId
findOrCreateLanguageMapping sourceLanguageKey targetLanguageKey = do
  languageMappingL <- select $ from $ \language_mappings -> do
    where_ (language_mappings ^. LanguageMappingSourceId ==. val sourceLanguageKey
            &&. language_mappings ^. LanguageMappingTargetId ==. val targetLanguageKey)
    return language_mappings
  case languageMappingL of
    [] -> insert LanguageMapping
      { languageMappingSourceId = sourceLanguageKey
      , languageMappingTargetId = targetLanguageKey
      }
    Entity key _ : _ -> return key

findOrCreateLogicMapping :: MonadIO m
                         => LogicId -> LogicId -> LanguageMappingId -> AnyComorphism
                         -> DBMonad m LogicMappingId
findOrCreateLogicMapping sourceLogicKey targetLogicKey languageMappingKey (Comorphism.Comorphism cid) = do
  let name = language_name cid
  let logicMappingSlugS = slugOfLogicMapping (Comorphism.Comorphism cid)
  logicMappingL <- select $ from $ \logic_mappings -> do
    where_ (logic_mappings ^. LogicMappingLanguageMappingId ==. val languageMappingKey
            &&. logic_mappings ^. LogicMappingSlug ==. val logicMappingSlugS)
    return logic_mappings
  case logicMappingL of
    [] -> insert LogicMapping
      { logicMappingLanguageMappingId = languageMappingKey
      , logicMappingSourceId = sourceLogicKey
      , logicMappingTargetId = targetLogicKey
      , logicMappingSlug = logicMappingSlugS
      , logicMappingName = name
      , logicMappingIsInclusion = isInclusionComorphism cid
      , logicMappingHasModelExpansion = has_model_expansion cid
      , logicMappingIsWeaklyAmalgamable = is_weakly_amalgamable cid
      }
    Entity key _ : _ -> return key

findLogicMappingByComorphism :: MonadIO m
                             => AnyComorphism
                             -> DBMonad m (Maybe (Entity LogicMapping))
findLogicMappingByComorphism comorphism =
  if isIdComorphism comorphism then return Nothing else do
    let logicMappingSlugS = slugOfLogicMapping comorphism
    findLogicMappingBySlug logicMappingSlugS

findLogicMappingBySlug :: MonadIO m
                       => String
                       -> DBMonad m (Maybe (Entity LogicMapping))
findLogicMappingBySlug logicMappingSlugS = do
  logicMappingL <- select $ from $ \ logic_mappings -> do
    where_ (logic_mappings ^. LogicMappingSlug ==. val logicMappingSlugS)
    return logic_mappings
  case logicMappingL of
    [] -> fail ("Persistence.LogicGraph.findLogicMappingBySlug: Could not find LogicMapping " ++ logicMappingSlugS)
    logicMappingEntity : _ -> return $ Just logicMappingEntity

exportReasoners :: MonadIO m => HetcatsOpts -> LogicGraph -> DBMonad m ()
exportReasoners _ logicGraph =
  mapM_ (\ (Logic.Logic lid) -> do
          let proversL = provers lid
          let consistencyCheckersL = cons_checkers lid
          mapM_ (findOrCreateProver . G_prover lid) proversL
          mapM_ (findOrCreateConsistencyChecker . G_cons_checker lid) consistencyCheckersL
        ) $ logics logicGraph

findOrCreateProver :: MonadIO m => G_prover -> DBMonad m ReasonerId
findOrCreateProver gProver = do
  let reasonerSlugS = slugOfProver gProver
  let name = getProverName gProver
  findOrCreateReasoner reasonerSlugS name Enums.Prover

findOrCreateConsistencyChecker :: MonadIO m => G_cons_checker -> DBMonad m ReasonerId
findOrCreateConsistencyChecker gConsistencyChecker = do
  let reasonerSlugS = slugOfConsistencyChecker gConsistencyChecker
  let name = getCcName gConsistencyChecker
  findOrCreateReasoner reasonerSlugS name Enums.ConsistencyChecker

findReasoner :: MonadIO m
             => String -> Enums.ReasonerKindType
             -> DBMonad m (Maybe (Entity Reasoner))
findReasoner reasonerSlugS reasonerKindValue = do
  reasonerL <-
    select $ from $ \ reasoners -> do
      where_ (reasoners ^. ReasonerSlug ==. val reasonerSlugS
              &&. reasoners ^. ReasonerKind ==. val reasonerKindValue)
      return reasoners
  case reasonerL of
    reasoner : _ -> return $ Just reasoner
    [] -> return Nothing

findOrCreateReasoner :: MonadIO m
                     => String -> String -> Enums.ReasonerKindType
                     -> DBMonad m ReasonerId
findOrCreateReasoner reasonerSlugS name reasonerKindValue = do
  reasonerM <- findReasoner reasonerSlugS reasonerKindValue
  case reasonerM of
    Just (Entity reasonerKey _) -> return reasonerKey
    Nothing -> insert Reasoner
      { reasonerSlug = reasonerSlugS
      , reasonerDisplayName = name
      , reasonerKind = reasonerKindValue
      }

findReasonerByGConsChecker :: MonadIO m
                           => G_cons_checker
                           -> DBMonad m (Entity Reasoner)
findReasonerByGConsChecker gConsChecker = do
  let reasonerSlugS = slugOfConsistencyChecker gConsChecker
  reasonerM <- findReasoner reasonerSlugS Enums.ConsistencyChecker
  case reasonerM of
    Nothing -> fail ("Persistence.LogicGraph.findReasonerByGConsChecker: Could not find Consistency Checker " ++ reasonerSlugS)
    Just reasonerEntity -> return reasonerEntity

findReasonerByGProver :: MonadIO m
                      => G_prover
                      -> DBMonad m (Entity Reasoner)
findReasonerByGProver gProver = do
  let reasonerSlugS = slugOfProver gProver
  reasonerM <- findReasoner reasonerSlugS Enums.Prover
  case reasonerM of
    Nothing -> fail ("Persistence.LogicGraph.findReasonerByGProver: Could not find Prover " ++ reasonerSlugS)
    Just reasonerEntity -> return reasonerEntity

findReasonerByProverOrConsChecker :: MonadIO m
                                  => ProverOrConsChecker
                                  -> DBMonad m (Entity Reasoner)
findReasonerByProverOrConsChecker reasoner = case reasoner of
  Prover gProver -> findReasonerByGProver gProver
  ConsChecker gConsChecker -> findReasonerByGConsChecker gConsChecker

findOrCreateLogicTranslation :: MonadIO m
                             => HetcatsOpts
                             -> AnyComorphism
                             -> DBMonad m (Maybe (Entity LogicTranslation))
findOrCreateLogicTranslation _ comorphism@(Comorphism.Comorphism cid) =
  if isIdComorphism comorphism
  then return Nothing
  else do
    let logicTranslationSlugS = slugOfTranslation comorphism
    let logicTranslationNameS = language_name cid
    translationL <- select $ from $ \ translations -> do
      where_ (translations ^. LogicTranslationSlug ==. val logicTranslationSlugS)
      return translations
    case translationL of
      translationEntity : _ -> return $ Just translationEntity
      [] -> do
        let logicTranslationValue = LogicTranslation
              { logicTranslationSlug = logicTranslationSlugS
              , logicTranslationName = logicTranslationNameS
              }
        logicTranslationKey <- insert logicTranslationValue
        mapM_ (\ (number, name) ->
                createLogicTranslationStep logicTranslationKey (number, name)
              ) $ zip [1..] $ constituents cid
        return $ Just $ Entity logicTranslationKey logicTranslationValue

createLogicTranslationStep :: MonadIO m
                           => LogicTranslationId
                           -> (Int, String)
                           -> DBMonad m (Entity LogicTranslationStep)
createLogicTranslationStep logicTranslationKey (number, name)
  | isInclusion_ name = do
      Entity logicInclusionKey _ <- findOrCreateLogicInclusion name
      let translationStepValue = LogicTranslationStep
            { logicTranslationStepLogicTranslationId = logicTranslationKey
            , logicTranslationStepNumber = number
            , logicTranslationStepLogicMappingId = Nothing
            , logicTranslationStepLogicInclusionId = Just logicInclusionKey
            }
      translationStepKey <- insert translationStepValue
      return $ Entity translationStepKey translationStepValue
  | otherwise = do
      Just (Entity logicMappingKey _) <-
        findLogicMappingBySlug $ slugOfLogicMappingByName name
      let translationStepValue = LogicTranslationStep
            { logicTranslationStepLogicTranslationId = logicTranslationKey
            , logicTranslationStepNumber = number
            , logicTranslationStepLogicMappingId = Just logicMappingKey
            , logicTranslationStepLogicInclusionId = Nothing
            }
      translationStepKey <- insert translationStepValue
      return $ Entity translationStepKey translationStepValue
  where
    isInclusion_ :: String -> Bool
    isInclusion_ name_ = "id_" `isPrefixOf` name_ || "incl_" `isPrefixOf` name_

findOrCreateLogicInclusion :: MonadIO m
                           => String
                           -> DBMonad m (Entity LogicInclusion)
findOrCreateLogicInclusion name = do
  let logicInclusionSlugS = slugOfLogicInclusionByName name
  logicInclusionL <- select $ from $ \ logic_inclusions -> do
    where_ (logic_inclusions ^. LogicInclusionSlug ==. val logicInclusionSlugS)
    return logic_inclusions
  case logicInclusionL of
    logicInclusionEntity : _ -> return logicInclusionEntity
    [] -> do
      let (languageSlugS, sourceSlugS, targetSlugM) = slugsFromName

      languageM <- findLanguage languageSlugS
      languageKey <- case languageM of
        Nothing -> fail ("Persistence.LogicGraph.findOrCreateLogicInclusion: "
          ++ "Could not find the language " ++ languageSlugS)
        Just (Entity key _) -> return key

      sourceM <- findLogic sourceSlugS
      sourceKey <- case sourceM of
        Nothing -> fail ("Persistence.LogicGraph.findOrCreateLogicInclusion: "
          ++ "Could not find the source logic " ++ sourceSlugS)
        Just (Entity key _) -> return key

      targetKeyM <- case targetSlugM of
        Nothing -> return Nothing
        Just targetSlugS -> do
          targetM <- findLogic targetSlugS
          case targetM of
            Nothing -> fail ("Persistence.LogicGraph.findOrCreateLogicInclusion: "
              ++ "Could not find the target logic " ++ targetSlugS)
            Just (Entity key _) -> return $ Just key

      let logicInclusionValue = LogicInclusion
            { logicInclusionSlug = logicInclusionSlugS
            , logicInclusionLanguageId = languageKey
            , logicInclusionSourceLogicId = sourceKey
            , logicInclusionTargetLogicId = targetKeyM
            }
      logicInclusionKey <- insert logicInclusionValue
      return $ Entity logicInclusionKey logicInclusionValue
  where
    slugsFromName :: (String, String, Maybe String)
    slugsFromName
      | "id_" `isPrefixOf` name =
          let languageName_ = takeWhile (/= '.') $ drop 3 name
              logicName_ = tail $ dropWhile (/= '.') name
              logicSlugS =
                slugOfLogicByName $ logicNameForDBByName languageName_ logicName_
          in  ( slugOfLanguageByName languageName_
              , logicSlugS
              , Nothing
              )
      | "incl_" `isPrefixOf` name =
          let languageName_ = takeWhile (/= ':') $ drop 5 name
              logicNames = tail $ dropWhile (/= ':') name
              [sourceName, targetName] = splitByList "->" logicNames
              sourceSlugS =
                slugOfLogicByName $ logicNameForDBByName languageName_ sourceName
              targetSlugS =
                slugOfLogicByName $ logicNameForDBByName languageName_ targetName
          in  ( slugOfLanguageByName languageName_
              , sourceSlugS
              , Just targetSlugS
              )
      | otherwise = error ("Persistence.LogicGraph.findOrCreateLogicInclusion.slugsFromName "
                           ++ "encountered a bad comorphism name: " ++ name)
