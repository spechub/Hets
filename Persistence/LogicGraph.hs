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
  languageL <- select $ from $ \languages -> do
    where_ (languages ^. LanguageSlug ==. val languageSlugS)
    return languages
  case languageL of
    [] -> insert Language
        { languageSlug = languageSlugS
        , languageName = show lid
        , languageDescription = description lid
        , languageStandardizationStatus = "TODO" -- TODO: add to class Logic
        , languageDefinedBy = "registry" -- TODO: add to class Logic (URL)
        }
    Entity key _ : _-> return key

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
  logicL <- select $ from $ \logicsSql -> do
    where_ (logicsSql ^. LogicSlug ==. val logicSlugS)
    return logicsSql
  case logicL of
    [] ->
      -- This is a two-staged process to save some performance:
      -- Case 1: If the logic existed beforehand, then we don't lock the
      -- database and return the logic ID. This is expected to happen very
      -- frequently.
      -- Case 2: If the logic did not exist at this point, we need to create
      -- it atomically. To do this, we do a find-or-create pattern inside a
      -- mutex. This is expected to happen only a few times.
      advisoryLocked opts migrateLogicGraphKey $ do
        logicL' <- select $ from $ \logicsSql -> do
          where_ (logicsSql ^. LogicSlug ==. val logicSlugS)
          return logicsSql
        case logicL' of
          [] -> insert SchemaClass.Logic
            { logicLanguageId = languageKey
            , logicSlug = logicSlugS
            , logicName = logicNameS
            }
          Entity key _ : _ -> return key
    Entity key _ : _ -> return key

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
  let logicMappingSlugS = parameterize name
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

sublogicNameForDB :: Logic.Logic lid sublogics basic_spec sentence symb_items
                       symb_map_items sign morphism symbol raw_symbol proof_tree
                  => lid -> sublogics -> String
sublogicNameForDB lid sublogic =
  let hetsName = sublogicName sublogic
  in  if null hetsName then show lid else hetsName
