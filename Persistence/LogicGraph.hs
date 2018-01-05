{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TypeFamilies               #-}
module Persistence.LogicGraph ( migrateLogicGraphKey
                              , exportLogicGraph
                              , findOrCreateLogic
                              , findOrCreateLanguageMappingAndLogicMapping
                              ) where

import Persistence.Database
import Persistence.Schema as SchemaClass
import Persistence.Utils

import qualified Comorphisms.LogicGraph as LogicGraph (logicGraph)
import Driver.Options
import Driver.Version
import Logic.Grothendieck
import Logic.Logic as Logic
import Logic.Comorphism as Comorphism

import Control.Monad (unless)
import Control.Monad.IO.Class (MonadIO (..))
import Database.Persist

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
    lastMigratedVersionM <- selectFirst [HetsKey ==. versionKeyName] []
    case lastMigratedVersionM of
      Nothing ->
        insert (Hets versionKeyName hetsVersionNumeric) >> migrateLogicGraph' opts
      Just (Entity _ value) ->
        unless (hetsValue value == hetsVersionNumeric) $ migrateLogicGraph' opts

migrateLogicGraph' :: MonadIO m => HetcatsOpts -> DBMonad m ()
migrateLogicGraph' opts = do
  exportLanguagesAndLogics opts LogicGraph.logicGraph
  exportLanguageMappingsAndLogicMappings opts LogicGraph.logicGraph

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
  let languageSlugS = parameterize $ show lid
  languageM <- selectFirst [LanguageSlug ==. languageSlugS] []
  case languageM of
    Just (Entity key _) -> return key
    Nothing -> insert Language
        { languageSlug = languageSlugS
        , languageName = show lid
        , languageDescription = description lid
        , languageStandardizationStatus = "TODO" -- TODO: add to class Logic
        , languageDefinedBy = "registry" -- TODO: add to class Logic (URL)
        }

findOrCreateLogic :: ( MonadIO m
                     , Logic.Logic lid sublogics basic_spec sentence
                         symb_items symb_map_items sign morphism symbol
                         raw_symbol proof_tree
                     )
                  => HetcatsOpts -> LanguageId -> lid -> sublogics
                  -> DBMonad m LogicId
findOrCreateLogic opts languageKey lid sublogic = do
  let logicNameS = sublogicNameForDB lid sublogic
  let logicSlugS = parameterize logicNameS
  logicM <- selectFirst [LogicSlug ==. logicSlugS] []
  case logicM of
    Just (Entity key _) -> return key
    Nothing ->
      -- This is a two-staged process to save some performance:
      -- Case 1: If the logic existed beforehand, then we don't lock the
      -- database and return the logic ID. This is expected to happen very
      -- frequently.
      -- Case 2: If the logic did not exist at this point, we need to create
      -- it atomically. To do this, we do a find-or-create pattern inside a
      -- mutex. This is expected to happen only a few times.
      advisoryLocked opts migrateLogicGraphKey $ do
        logicM' <- selectFirst [LogicSlug ==. logicSlugS] []
        case logicM' of
          Just (Entity key _) -> return key
          Nothing -> insert SchemaClass.Logic
            { logicLanguageId = languageKey
            , logicSlug = logicSlugS
            , logicName = logicNameS
            }

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
  let sourceLanguageSlugS = parameterize $ show $ sourceLogic cid
      targetLanguageSlugS = parameterize $ show $ targetLogic cid
  in do
    -- Find the IDs in the databases:
    Just (Entity sourceLanguageKey _) <-
          selectFirst [LanguageSlug ==. sourceLanguageSlugS] []
    Just (Entity targetLanguageKey _) <-
          selectFirst [LanguageSlug ==. targetLanguageSlugS] []

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
  languageMappingM <-
    selectFirst [ LanguageMappingSourceId ==. sourceLanguageKey
                , LanguageMappingTargetId ==. targetLanguageKey
                ] []
  case languageMappingM of
    Just (Entity key _) -> return key
    Nothing -> insert LanguageMapping
      { languageMappingSourceId = sourceLanguageKey
      , languageMappingTargetId = targetLanguageKey
      }

findOrCreateLogicMapping :: MonadIO m
                         => LogicId -> LogicId -> LanguageMappingId -> AnyComorphism
                         -> DBMonad m LogicMappingId
findOrCreateLogicMapping sourceLogicKey targetLogicKey languageMappingKey (Comorphism.Comorphism cid) = do
  let name = language_name cid
  let logicMappingSlugS = parameterize name
  logicMappingM <-
    selectFirst [ LogicMappingLanguageMappingId ==. languageMappingKey
                , LogicMappingSlug ==. logicMappingSlugS
                ] []
  case logicMappingM of
    Just (Entity key _) -> return key
    Nothing -> insert LogicMapping
      { logicMappingLanguageMappingId = languageMappingKey
      , logicMappingSourceId = sourceLogicKey
      , logicMappingTargetId = targetLogicKey
      , logicMappingSlug = logicMappingSlugS
      , logicMappingName = name
      , logicMappingIsInclusion = isInclusionComorphism cid
      , logicMappingHasModelExpansion = has_model_expansion cid
      , logicMappingIsWeaklyAmalgamable = is_weakly_amalgamable cid
      }

sublogicNameForDB :: Logic.Logic lid sublogics basic_spec sentence symb_items
                       symb_map_items sign morphism symbol raw_symbol proof_tree
                  => lid -> sublogics -> String
sublogicNameForDB lid sublogic =
  let hetsName = sublogicName sublogic
  in  if null hetsName then show lid else hetsName
