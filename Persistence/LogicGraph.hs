{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TypeFamilies               #-}
module Persistence.LogicGraph where

import Persistence.Database
import Persistence.Schema as SchemaClass
import Persistence.Utils

import qualified Comorphisms.LogicGraph as LogicGraph (logicGraph)
import Driver.Version
import Logic.Grothendieck
import Logic.Logic as Logic
import Logic.Comorphism as Comorphism

import Control.Monad (unless)
import Control.Monad.IO.Class (MonadIO (..))
import Database.Persist
import Database.Persist.Sql

import Debug.Trace

migrateLanguages :: ( MonadIO m
                    , IsSqlBackend backend
                    , PersistQueryRead backend
                    , PersistStoreWrite backend
                    )
                 => DBMonad backend m ()
migrateLanguages = do
  let versionKeyName = "lastMigratedVersion"
  lastMigratedVersionM <- selectFirst [HetsKey ==. versionKeyName] []
  case lastMigratedVersionM of
    Nothing ->
      insert (Hets versionKeyName hetsVersionNumeric) >> exportLogicGraph
    Just (Entity _ value) ->
      unless (hetsValue value == hetsVersionNumeric) exportLogicGraph

exportLogicGraph :: ( MonadIO m
                    , IsSqlBackend backend
                    , PersistQueryRead backend
                    , PersistStoreWrite backend
                    )
                 => DBMonad backend m ()
exportLogicGraph = do
  exportLanguagesAndLogics LogicGraph.logicGraph
  exportLanguageMappingsAndLogicMappings LogicGraph.logicGraph

-- Export all Languages and Logics. Add those that have been added since a
-- previous version of Hets. This does not delete Languages or Logics.
exportLanguagesAndLogics :: ( MonadIO m
                            , IsSqlBackend backend
                            , PersistQueryRead backend
                            , PersistStoreWrite backend
                            )
                         => LogicGraph -> DBMonad backend m ()
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
                  let logicSlugS = parameterize $ sublogicName sublogic
                  logicM <- selectFirst [LogicSlug ==. logicSlugS] []
                  case logicM of
                    Just (Entity key _) -> return key
                    Nothing -> insert SchemaClass.Logic
                      { logicLanguageId = languageKey
                      , logicSlug = logicSlugS
                      , logicName = sublogicName sublogic
                      }
                ) $ all_sublogics lid
        ) $ logics logicGraph

-- Export all LanguageMappings and LogicMappings. Add those that have been added
-- since a previous version of Hets. This does not delete any of the old
-- mappings.
exportLanguageMappingsAndLogicMappings :: ( MonadIO m
                                          , IsSqlBackend backend
                                          , PersistQueryRead backend
                                          , PersistStoreWrite backend
                                          )
                                       => LogicGraph -> DBMonad backend m ()
exportLanguageMappingsAndLogicMappings logicGraph =
  mapM_ findOrCreateLanguageMappingAndLogicMapping $ comorphisms logicGraph

findOrCreateLanguageMappingAndLogicMapping :: ( MonadIO m
                                              , IsSqlBackend backend
                                              , PersistQueryRead backend
                                              , PersistStoreWrite backend
                                              )
                                           => AnyComorphism
                                           -> DBMonad backend m
                                                      ( LanguageMappingId
                                                      , LogicMappingId
                                                      )
findOrCreateLanguageMappingAndLogicMapping (Comorphism.Comorphism cid) =
          let name = language_name cid
              logicMappingSlugS = parameterize name
              sourceLanguageSlugS = parameterize $ show $ sourceLogic cid
              targetLanguageSlugS = parameterize $ show $ targetLogic cid
              sourceLogicSlugS = parameterize $ sublogicName $ sourceSublogic cid
              targetLogicSlugS = parameterize $ sublogicName $ targetSublogic cid
          in do
            -- Find the IDs in the databases:
            Just (Entity sourceLanguageKey _) <-
                  selectFirst [LanguageSlug ==. sourceLanguageSlugS] []
            Just (Entity targetLanguageKey _) <-
                  selectFirst [LanguageSlug ==. targetLanguageSlugS] []
            -- Just (Entity sourceLogicKey _) <-
            --       selectFirst [LogicSlug ==. sourceLogicSlugS] []
            -- Just (Entity targetLogicKey _) <-
            --       selectFirst [LogicSlug ==. targetLogicSlugS] []
            -- -----------------------------------------------------------------

            -- findOrCreateLogic (source):
            sourceLogicM <- selectFirst [LogicSlug ==. sourceLogicSlugS] []
            sourceLogicKey <- case sourceLogicM of
                Nothing -> trace ("Could not find sublogic " ++ sublogicName (sourceSublogic cid) ++ " used as the source sublogic by the comorphism " ++ name) $ do
                  -- TODO: do not insert the sublogic as soon as https://github.com/spechub/Hets/issues/1740 is fixed
                  let sublogic = sourceSublogic cid
                  let logicSlugS = parameterize $ sublogicName sublogic
                  logicM <- selectFirst [LogicSlug ==. logicSlugS] []
                  case logicM of
                    Just (Entity key _) -> return key
                    Nothing -> insert SchemaClass.Logic
                      { logicLanguageId = sourceLanguageKey
                      , logicSlug = logicSlugS
                      , logicName = sublogicName $ sourceSublogic cid
                      }
                Just (Entity t _) -> return t

            -- findOrCreateLogic (target):
            targetLogicM <- selectFirst [LogicSlug ==. targetLogicSlugS] []
            targetLogicKey <- case targetLogicM of
                Nothing -> trace ("Could not find sublogic " ++ sublogicName (targetSublogic cid) ++ " used as the target sublogic by the comorphism " ++ show name) $ do
                  -- TODO: do not insert the sublogic as soon as https://github.com/spechub/Hets/issues/1740 is fixed
                  let sublogic = targetSublogic cid
                  let logicSlugS = parameterize $ sublogicName sublogic
                  logicM <- selectFirst [LogicSlug ==. logicSlugS] []
                  case logicM of
                    Just (Entity key _) -> return key
                    Nothing -> insert SchemaClass.Logic
                      { logicLanguageId = targetLanguageKey
                      , logicSlug = logicSlugS
                      , logicName = sublogicName $ targetSublogic cid
                      }
                Just (Entity t _) -> return t
            -- -----------------------------------------------------------------

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
