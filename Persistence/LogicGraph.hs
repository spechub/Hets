{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TypeFamilies               #-}
module Persistence.LogicGraph where

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
  exportLanguagesAndLogics LogicGraph.logicGraph
  exportLanguageMappingsAndLogicMappings opts LogicGraph.logicGraph

-- Export all Languages and Logics. Add those that have been added since a
-- previous version of Hets. This does not delete Languages or Logics.
exportLanguagesAndLogics :: MonadIO m
                         => LogicGraph -> DBMonad m ()
exportLanguagesAndLogics logicGraph =
  mapM_ (\ (Logic.Logic lid) -> do
          let languageSlugS = parameterize $ show lid
          languageM <- selectFirst [LanguageSlug ==. languageSlugS] []
          languageKey <- case languageM of
            Just (Entity key _) -> return key
            Nothing -> do
              -- Export Language
              insert Language
                { languageSlug = languageSlugS
                , languageName = show lid
                , languageDescription = description lid
                , languageStandardizationStatus = "TODO" -- TODO: add to class Logic
                , languageDefinedBy = "registry" -- TODO: add to class Logic (URL)
                }

          -- Export Logic
          mapM_ (\ sublogic -> do
                  let logicNameS = sublogicNameForDB lid sublogic
                  let logicSlugS = parameterize logicNameS
                  logicM <- selectFirst [LogicSlug ==. logicSlugS] []
                  case logicM of
                    Just (Entity key _) -> return key
                    Nothing -> insert SchemaClass.Logic
                      { logicLanguageId = languageKey
                      , logicSlug = logicSlugS
                      , logicName = logicNameS
                      }
                ) $ all_sublogics lid
        ) $ logics logicGraph

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
                                           => HetcatsOpts
                                           -> AnyComorphism
                                           -> DBMonad m ( LanguageMappingId
                                                        , LogicMappingId
                                                        )
findOrCreateLanguageMappingAndLogicMapping opts (Comorphism.Comorphism cid) =
          let name = language_name cid
              logicMappingSlugS = parameterize name
              sourceLanguageSlugS = parameterize $ show $ sourceLogic cid
              targetLanguageSlugS = parameterize $ show $ targetLogic cid
              sourceLogicName = sublogicNameForDB (sourceLogic cid) $ sourceSublogic cid
              targetLogicName = sublogicNameForDB (targetLogic cid) $ targetSublogic cid
              sourceLogicSlugS = parameterize sourceLogicName
              targetLogicSlugS = parameterize targetLogicName
          in do
            -- Find the IDs in the databases:
            Just (Entity sourceLanguageKey _) <-
                  selectFirst [LanguageSlug ==. sourceLanguageSlugS] []
            Just (Entity targetLanguageKey _) <-
                  selectFirst [LanguageSlug ==. targetLanguageSlugS] []

            -- findOrCreateLogic (source):
            sourceLogicM <- selectFirst [LogicSlug ==. sourceLogicSlugS] []
            sourceLogicKey <- case sourceLogicM of
                Nothing -> do
                  -- TODO: do not insert the sublogic as soon as https://github.com/spechub/Hets/issues/1740 is fixed
                  logicM <- selectFirst [LogicSlug ==. sourceLogicSlugS] []
                  case logicM of
                    Just (Entity key _) -> return key
                    Nothing -> advisoryLocked opts migrateLogicGraphKey $
                      insert SchemaClass.Logic
                        { logicLanguageId = sourceLanguageKey
                        , logicSlug = sourceLogicSlugS
                        , logicName = sourceLogicName
                        }
                Just (Entity t _) -> return t

            -- findOrCreateLogic (target):
            targetLogicM <- selectFirst [LogicSlug ==. targetLogicSlugS] []
            targetLogicKey <- case targetLogicM of
                Nothing -> do
                  -- TODO: do not insert the sublogic as soon as https://github.com/spechub/Hets/issues/1740 is fixed
                  logicM <- selectFirst [LogicSlug ==. targetLogicSlugS] []
                  case logicM of
                    Just (Entity key _) -> return key
                    Nothing -> advisoryLocked opts migrateLogicGraphKey $
                      insert SchemaClass.Logic
                        { logicLanguageId = targetLanguageKey
                        , logicSlug = targetLogicSlugS
                        , logicName = targetLogicName
                        }
                Just (Entity t _) -> return t

            -- findOrCreateLanguageMapping:
            languageMappingM <-
              selectFirst [ LanguageMappingSourceId ==. sourceLanguageKey
                          , LanguageMappingTargetId ==. targetLanguageKey
                          ] []
            languageMappingKey <- case languageMappingM of
              Just (Entity key _) -> return key
              Nothing -> insert LanguageMapping
                { languageMappingSourceId = sourceLanguageKey
                , languageMappingTargetId = targetLanguageKey
                }

            -- findOrCreateLogicMapping:
            logicMappingM <-
              selectFirst [ LogicMappingLanguageMappingId ==. languageMappingKey
                          , LogicMappingSlug ==. logicMappingSlugS
                          ] []
            case logicMappingM of
              Just (Entity key _) -> return (languageMappingKey, key)
              Nothing -> do
                logicMappingKey <- insert LogicMapping
                  { logicMappingLanguageMappingId = languageMappingKey
                  , logicMappingSourceId = sourceLogicKey
                  , logicMappingTargetId = targetLogicKey
                  , logicMappingSlug = logicMappingSlugS
                  , logicMappingName = name
                  , logicMappingIsInclusion = isInclusionComorphism cid
                  , logicMappingHasModelExpansion = has_model_expansion cid
                  , logicMappingIsWeaklyAmalgamable = is_weakly_amalgamable cid
                  }
                return (languageMappingKey, logicMappingKey)

sublogicNameForDB :: Logic.Logic lid sublogics basic_spec sentence symb_items
                       symb_map_items sign morphism symbol raw_symbol proof_tree
                  => lid -> sublogics -> String
sublogicNameForDB lid sublogic =
  let hetsName = sublogicName sublogic
  in  if null hetsName then show lid else hetsName
