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
                              , findReasonerByGProver
                              ) where

import Persistence.Database
import Persistence.Schema as DatabaseSchema
import Persistence.Utils
import qualified Persistence.Schema.Enums as Enums

import qualified Comorphisms.LogicGraph as LogicGraph (logicGraph)
import Driver.Options
import Driver.Version
import Logic.Grothendieck
import Logic.Logic as Logic
import Logic.Comorphism as Comorphism
import Proofs.AbstractState (G_prover (..), G_cons_checker (..), getProverName, getCcName)

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
          [] -> insert DatabaseSchema.Logic
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
findLogicMappingByComorphism comorphism@(Comorphism.Comorphism cid) =
  if isIdComorphism comorphism then return Nothing else do
    let logicMappingSlugS = slugOfLogicMapping comorphism
    logicMappingL <- select $ from $ \ logic_mappings -> do
      where_ (logic_mappings ^. LogicMappingSlug ==. val logicMappingSlugS)
      return logic_mappings
    case logicMappingL of
      [] -> fail ("Persistence.LogicGraph.findLogicMappingByComorphism: Could not find LogicMapping " ++ logicMappingSlugS)
      logicMappingEntity : _ -> return $ Just logicMappingEntity

findOrCreateLogicTranslation :: MonadIO m
                        => HetcatsOpts
                        -> AnyComorphism
                        -> DBMonad m (Maybe (Entity LogicTranslation))
findOrCreateLogicTranslation opts comorphism@(Comorphism.Comorphism cid) =
  if isIdComorphism comorphism
  then return Nothing
  else do
    let logicTranslationSlugS = slugOfTranslation comorphism
    translationL <- select $ from $ \ translations -> do
      where_ (translations ^. LogicTranslationSlug ==. val logicTranslationSlugS)
      return translations
    case translationL of
      translationEntity : _ -> return $ Just translationEntity
      [] -> do
        let logicTranslationValue =
              LogicTranslation { logicTranslationSlug = logicTranslationSlugS }
        logicTranslationKey <- insert logicTranslationValue
        mapM_ (\ (number, Comorphism.Comorphism cid) ->
                createLogicTranslationStep opts logicTranslationKey (number, cid)
              ) $ zip [1..] $ flattenComposition cid
        return $ Just $ Entity logicTranslationKey logicTranslationValue


sublogicNameForDB :: Logic.Logic lid sublogics basic_spec sentence symb_items
                       symb_map_items sign morphism symbol raw_symbol proof_tree
                  => lid -> sublogics -> String
sublogicNameForDB lid sublogic =
  let hetsName = sublogicName sublogic
  in  if null hetsName then show lid else hetsName

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

findReasonerByGProver :: MonadIO m
                      => G_prover
                      -> DBMonad m (Entity Reasoner)
findReasonerByGProver gProver = do
  let reasonerSlugS = slugOfProver gProver
  reasonerM <- findReasoner reasonerSlugS Enums.Prover
  case reasonerM of
    Nothing -> fail ("Persistence.LogicGraph.findReasonerByGProver: Could not find Prover " ++ reasonerSlugS)
    Just reasonerEntity -> return reasonerEntity


class Comorphism cid
                lid1 sublogics1 basic_spec1 sentence1
                symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
                lid2 sublogics2 basic_spec2 sentence2
                symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2 =>
  FlattenComposition cid  lid1 sublogics1 basic_spec1 sentence1
            symb_items1 symb_map_items1
            sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2
            symb_items2 symb_map_items2
            sign2 morphism2 symbol2 raw_symbol2 proof_tree2
  where
    flattenComposition :: cid -> [AnyComorphism]
    flattenComposition cid = [Comorphism.Comorphism cid]

instance (Comorphism cid1
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2,
          Comorphism cid2
            lid4 sublogics4 basic_spec4 sentence4 symb_items4 symb_map_items4
                sign4 morphism4 symbol4 raw_symbol4 proof_tree4
            lid3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3)
          => FlattenComposition (CompComorphism cid1 cid2)
               lid1 sublogics1 basic_spec1 sentence1
               symb_items1 symb_map_items1
               sign1 morphism1 symbol1 raw_symbol1 proof_tree1
               lid2 sublogics2 basic_spec2 sentence2
               symb_items2 symb_map_items2
               sign2 morphism2 symbol2 raw_symbol2 proof_tree2
  where
    flattenComposition (CompComorphism cid1 cid2) =
      flattenComposition cid1 ++ flattenComposition cid2

-- This class expects all comorphisms to be in the LogicGraph except for
-- Inclusions and Compositions
class Comorphism cid
                lid1 sublogics1 basic_spec1 sentence1
                symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
                lid2 sublogics2 basic_spec2 sentence2
                symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2 =>
  CreateLogicTranslationStep cid  lid1 sublogics1 basic_spec1 sentence1
            symb_items1 symb_map_items1
            sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2
            symb_items2 symb_map_items2
            sign2 morphism2 symbol2 raw_symbol2 proof_tree2
  where
    createLogicTranslationStep :: MonadIO m
                               => HetcatsOpts
                               -> LogicTranslationId
                               -> (Int, cid)
                               -> DBMonad m (Entity LogicTranslationStep)
    createLogicTranslationStep opts logicTranslationKey (number, cid) = do
      Just (Entity logicMappingKey _) <-
        findLogicMappingByComorphism (Comorphism.Comorphism cid)
      return LogicTranslationStep
        { logicTranslationStepTranslationId = logicTranslationKey
        , logicTranslationStepNumber = number
        , logicTranslationStepLogicMappingId = Just logicMappingKey
        , logicTranslationStepLogicInclusionId = Nothing
        }
      translationStepKey <- insert translationStepValue
      return $ Entity translationStepKey translationStepValue

instance CreateLogicTranslationStep (InclComorphism lid sublogics)
           lid1 sublogics1 basic_spec1 sentence1
           symb_items1 symb_map_items1
           sign1 morphism1 symbol1 raw_symbol1 proof_tree1
           lid2 sublogics2 basic_spec2 sentence2
           symb_items2 symb_map_items2
           sign2 morphism2 symbol2 raw_symbol2 proof_tree2
  where
    createLogicTranslationStep opts logicTranslationKey (number, cid) = do
      languageKey <- findOrCreateLanguage lid
      sourceLogicKey <- findOrCreateLogic opts languageKey lid sourceSublogic
      targetLogicKey <- findOrCreateLogic opts languageKey lid targetSublogic
      logicInclusionKey <- insert LogicInclusion
        { logicInclusionSourceLogicId = sourceLogicKey
        , logicInclusionTargetLogicId = targetLogicKey
        }
      let translationStepValue = LogicTranslationStep
           { logicTranslationStepTranslationId = logicTranslationKey
           , logicTranslationStepNumber = number
           , logicTranslationStepLogicMappingId = Nothing
           , logicTranslationStepLogicInclusionId = Just logicInclusionKey
           }
      translationStepKey <- insert translationStepValue
      return $ Entity translationStepKey translationStepValue


instance (Comorphism cid1
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2,
          Comorphism cid2
            lid4 sublogics4 basic_spec4 sentence4 symb_items4 symb_map_items4
                sign4 morphism4 symbol4 raw_symbol4 proof_tree4
            lid3 sublogics3 basic_spec3 sentence3 symb_items3 symb_map_items3
                sign3 morphism3 symbol3 raw_symbol3 proof_tree3)
          => CreateLogicTranslationStep (CompComorphism cid1 cid2)
               lid1 sublogics1 basic_spec1 sentence1
               symb_items1 symb_map_items1
               sign1 morphism1 symbol1 raw_symbol1 proof_tree1
               lid2 sublogics2 basic_spec2 sentence2
               symb_items2 symb_map_items2
               sign2 morphism2 symbol2 raw_symbol2 proof_tree2
  where
    createLogicTranslationStep _ _ _ =
      fail ("Persistence.LogicGraph.createLogicTranslationStep: "
            ++ "Flattening CompComorphisms has failed")
