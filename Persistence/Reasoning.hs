{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ScopedTypeVariables        #-}

module Persistence.Reasoning ( setupReasoning
                             , preprocessReasoning
                             , postprocessReasoning
                             ) where

import Persistence.Database
import Persistence.LogicGraph
import Persistence.Schema as DatabaseSchema
import qualified Persistence.Schema.Enums as Enums
import qualified Persistence.Schema.ConsistencyStatusType as ConsistencyStatusType
import qualified Persistence.Schema.EvaluationStateType as EvaluationStateType
import Persistence.Utils

import Persistence.Reasoning.PremiseSelectionSInE as SInE
import PGIP.ReasoningParameters as ReasoningParameters
import PGIP.Shared

import Driver.Options
import qualified Logic.Prover as LP
import Proofs.AbstractState (G_proof_tree)
import Static.DevGraph
import Static.GTheory

import Control.Exception (catch)
import Control.Exception.Base (SomeException)
import Control.Monad.IO.Class (MonadIO (..))
import Data.Char (toLower)
import Data.Maybe as Maybe (fromJust, fromMaybe, isNothing)
import Data.List (elemIndex, isPrefixOf, isInfixOf, maximumBy)
import qualified Data.Text as Text
import Data.Time.LocalTime
import Database.Persist hiding ((==.))
import Database.Persist.Sql hiding ((==.))
import Database.Esqueleto hiding ((=.), update)
import qualified Database.Esqueleto as E ((=.), update)

setupReasoning :: HetcatsOpts
               -> ReasoningCacheGoal
               -> IO (Maybe ReasonerConfigurationId)
setupReasoning opts reasoningCacheGoal
  | rceUseDatabase reasoningCacheGoal = onDatabase (databaseConfig opts) $
      fmap Just $ createReasonerConfiguration reasoningCacheGoal
  | otherwise = return Nothing

createReasonerConfiguration :: MonadIO m
                            => ReasoningCacheGoal
                            -> DBMonad m ReasonerConfigurationId
createReasonerConfiguration reasoningCacheGoal = do
  reasonerEntityM <-
    case reasoner $ reasonerConfiguration $ rceGoalConfig reasoningCacheGoal of
      Nothing -> return Nothing
      Just reasonerName -> findReasoner reasonerName Enums.Prover
  let reasonerKeyM = fmap (\ (Entity key _) -> key) reasonerEntityM
  insert DatabaseSchema.ReasonerConfiguration
    { reasonerConfigurationConfiguredReasonerId = reasonerKeyM
    , reasonerConfigurationTimeLimit = Just $
        timeLimit $ reasonerConfiguration $ rceGoalConfig reasoningCacheGoal
    }

preprocessReasoning :: HetcatsOpts
                    -> String
                    -> ReasoningCacheGoal
                    -> IO (Maybe [String], ReasoningCacheGoal)
preprocessReasoning opts location reasoningCacheGoal = do
  premiseSelectionResultData@(premisesM, _, _) <-
    case rceProverMode reasoningCacheGoal of
      GlConsistency -> return (Nothing, 0, NoResult)
      GlProofs ->
        case premiseSelection $ rceGoalConfig reasoningCacheGoal of
          Nothing -> return (Nothing, 0, NoResult)
          Just premiseSelectionParameters -> do
            let premiseSelectionKindV =
                  getPremiseSelectionKind premiseSelectionParameters
            let gTheory = rceGTheory reasoningCacheGoal
            let goalName = fromJust $ rceGoalNameM reasoningCacheGoal
            performPremiseSelection opts gTheory goalName
              premiseSelectionParameters premiseSelectionKindV

  reasoningCacheGoal' <- case rceReasonerConfigurationKeyM reasoningCacheGoal of
    Nothing -> return reasoningCacheGoal
    Just _ -> do
      Entity reasoningAttemptKey _ <-
        onDatabase (databaseConfig opts) $ do
          (reasoningAttemptEntity, omsEntity) <-
            createReasoningAttempt opts location reasoningCacheGoal
          case rceProverMode reasoningCacheGoal of
            GlConsistency -> return ()
            GlProofs -> case premiseSelection $ rceGoalConfig reasoningCacheGoal of
              Nothing -> return ()
              Just premiseSelectionParameters -> do
                let premiseSelectionKindV =
                      getPremiseSelectionKind premiseSelectionParameters
                createPremiseSelection opts
                  reasoningAttemptEntity premiseSelectionParameters
                  premiseSelectionKindV premiseSelectionResultData omsEntity
          return reasoningAttemptEntity
      return reasoningCacheGoal { rceReasoningAttemptKeyM = Just reasoningAttemptKey }
  return (premisesM, reasoningCacheGoal')

getPremiseSelectionKind :: ReasoningParameters.PremiseSelection
                        -> Enums.PremiseSelectionKindType
getPremiseSelectionKind premiseSelectionParameters =
  case map toLower $ kind premiseSelectionParameters of
    "sine" -> Enums.SinePremiseSelection
    _ -> Enums.ManualPremiseSelection

data PremiseSelectionResultForDatabase = NoResult
                                       | SineResult SInE.G_SInEResult

performPremiseSelection :: HetcatsOpts
                        -> G_theory
                        -> String
                        -> ReasoningParameters.PremiseSelection
                        -> Enums.PremiseSelectionKindType
                        -> IO (Maybe [String], Int, PremiseSelectionResultForDatabase)
performPremiseSelection opts gTheory
  goalName premiseSelectionParameters premiseSelectionKindV =
  case premiseSelectionKindV of
    Enums.ManualPremiseSelection ->
      return (manualPremises premiseSelectionParameters, 0, NoResult)
    Enums.SinePremiseSelection -> do
      (premisesM, timeTaken, sineResult) <-
        SInE.perform opts gTheory premiseSelectionParameters goalName
      return (premisesM, timeTaken, SineResult sineResult)

createReasoningAttempt :: forall m . MonadIO m
                       => HetcatsOpts
                       -> String
                       -> ReasoningCacheGoal
                       -> DBMonad m (Entity ReasoningAttempt, Entity LocIdBase)
createReasoningAttempt opts location reasoningCacheGoal = do
  let nodeLabel = snd $ rceNode reasoningCacheGoal
  let reasoner_ = rceReasoner reasoningCacheGoal
  let comorphism = rceComorphism reasoningCacheGoal
  documentEntity <- findDocument opts location
  omsEntity <- findOMS documentEntity nodeLabel
  Entity reasonerKey _ <- findReasonerByProverOrConsChecker reasoner_
  logicTranslationEntityM <- findOrCreateLogicTranslation opts comorphism
  reasoningAttemptEntity <- case rceProverMode reasoningCacheGoal of
    GlConsistency ->
      advisoryLocked opts (omsLockKey $ entityKey omsEntity) $ do
        setOmsEvaluationState omsEntity EvaluationStateType.Processing
        reasoningAttemptEntity@(Entity reasoningAttemptKey _) <- insertReasoningAttempt
          Enums.ConsistencyCheckAttempt
          EvaluationStateType.Processing
          Nothing
          (Just reasonerKey)
          (fmap entityKey logicTranslationEntityM)
        let consistencyCheckAttemptKey = toSqlKey $ fromSqlKey reasoningAttemptKey
        let consistencyCheckAttemptValue = DatabaseSchema.ConsistencyCheckAttempt
              { consistencyCheckAttemptOmsId = Just $ entityKey omsEntity
              , consistencyCheckAttemptConsistencyStatus =
                  ConsistencyStatusType.Open
              }
        insertEntityMany
          [Entity consistencyCheckAttemptKey consistencyCheckAttemptValue]
        return reasoningAttemptEntity
    GlProofs -> do
      let goalName = fromJust $ rceGoalNameM reasoningCacheGoal
      conjectureKeyOrError <- liftIO $ Control.Exception.catch
        (do
          Entity conjectureKey _ <- onDatabase (databaseConfig opts) $
            findConjecture omsEntity goalName
          return $ Right conjectureKey
        )
        (\ exception ->
          return $ Left ("Persistence.Reasoning.createReasoningAttempt: "
                         ++ "Could not find conjecture \"" ++ goalName
                         ++ "\" - " ++ show (exception :: SomeException))
        )
      (reasoningAttemptEntity@(Entity reasoningAttemptKey _), conjectureKeyM, status) <-
        case conjectureKeyOrError of
          Right conjectureKey -> do
            Just conjectureValue <- get conjectureKey
            let conjectureEntity = Entity conjectureKey conjectureValue
            advisoryLocked opts (conjectureLockKey conjectureKey) $ do
              setConjectureEvaluationState
                conjectureEntity EvaluationStateType.Processing
              reasoningAttemptEntity <- insertReasoningAttempt
                Enums.ProofAttempt
                EvaluationStateType.Processing
                Nothing
                (Just reasonerKey)
                (fmap entityKey logicTranslationEntityM)
              return (reasoningAttemptEntity, Just conjectureKey, Enums.OPN)
          Left message -> do
            reasoningAttemptEntity <- insertReasoningAttempt
              Enums.ProofAttempt
              EvaluationStateType.FinishedUnsuccessfully
              (Just message)
              (Just reasonerKey)
              (fmap entityKey logicTranslationEntityM)
            return (reasoningAttemptEntity, Nothing, Enums.ERR)
      let proofAttemptKey = toSqlKey $ fromSqlKey reasoningAttemptKey
      let proofAttemptValue = DatabaseSchema.ProofAttempt
            { proofAttemptConjectureId = conjectureKeyM
            , proofAttemptProofStatus = status
            }
      insertEntityMany [Entity proofAttemptKey proofAttemptValue]
      return reasoningAttemptEntity
  return (reasoningAttemptEntity, omsEntity)
  where
    insertReasoningAttempt :: MonadIO m
                           => Enums.ReasoningAttemptKindType
                           -> EvaluationStateType.EvaluationStateType
                           -> Maybe String
                           -> Maybe DatabaseSchema.ReasonerId
                           -> Maybe DatabaseSchema.LogicTranslationId
                           -> DBMonad m (Entity ReasoningAttempt)
    insertReasoningAttempt kind_ evaluationState messageM reasonerKey
      logicTranslationKey = do
      actionKey <- insert DatabaseSchema.Action
        { actionEvaluationState = evaluationState
        , actionMessage = fmap Text.pack messageM
        }
      let reasoningAttemptValue = DatabaseSchema.ReasoningAttempt
            { reasoningAttemptKind = kind_
            , reasoningAttemptActionId = actionKey
            , reasoningAttemptReasonerConfigurationId =
                fromJust $ rceReasonerConfigurationKeyM reasoningCacheGoal
            , reasoningAttemptUsedReasonerId = reasonerKey
            , reasoningAttemptUsedLogicTranslationId = logicTranslationKey
            , reasoningAttemptTimeTaken = Nothing
            }
      reasoningAttemptKey <- insert reasoningAttemptValue
      return (Entity reasoningAttemptKey reasoningAttemptValue)

createPremiseSelection :: MonadIO m
                       => HetcatsOpts
                       -> Entity ReasoningAttempt
                       -> ReasoningParameters.PremiseSelection
                       -> Enums.PremiseSelectionKindType
                       -> (Maybe [String], Int, PremiseSelectionResultForDatabase)
                       -> Entity LocIdBase
                       -> DBMonad m ()
createPremiseSelection opts
  (Entity reasoningAttemptKey reasoningAttemptValue)
  premiseSelectionParameters premiseSelectionKindV
  (premisesM, timeTaken, premiseSelectionResult) omsEntity = do
  let premises = fromMaybe [] premisesM
  let proofAttemptKey = toSqlKey $ fromSqlKey reasoningAttemptKey
  let premiseSelectionValue = DatabaseSchema.PremiseSelection
        { premiseSelectionReasonerConfigurationId =
            reasoningAttemptReasonerConfigurationId reasoningAttemptValue
        , premiseSelectionProofAttemptId = proofAttemptKey
        , premiseSelectionKind = premiseSelectionKindV
        , premiseSelectionTimeTaken = Just timeTaken
        }
  premiseSelectionKey <- insert premiseSelectionValue
  createSpecificPremiseSelection premiseSelectionKey
  mapM_ (\ premiseName -> do
          premiseKeyM <- liftIO $ Control.Exception.catch
            (do
              premiseKey <- onDatabase (databaseConfig opts) $
                findPremise omsEntity premiseName
              return $ Just premiseKey
            )
            (\ exception -> do
              return (exception :: SomeException) -- GHC needs this line
              return Nothing
            )
          case premiseKeyM of
            Just (Entity premiseKey _) -> do
              insert DatabaseSchema.PremiseSelectedSentence
                { premiseSelectedSentencePremiseId = premiseKey
                , premiseSelectedSentencePremiseSelectionId = premiseSelectionKey
                }
              return ()
            Nothing -> return ()
        ) premises
  where
    createSpecificPremiseSelection premiseSelectionKey = case premiseSelectionKindV of
      Enums.ManualPremiseSelection ->
        insertEntityMany [Entity (toSqlKey $ fromSqlKey premiseSelectionKey)
                                 DatabaseSchema.ManualPremiseSelection]
      Enums.SinePremiseSelection -> do
        let sinePremiseSelectionKey = toSqlKey $ fromSqlKey premiseSelectionKey
        insertEntityMany
          [Entity sinePremiseSelectionKey
                  DatabaseSchema.SinePremiseSelection
                    { sinePremiseSelectionDepthLimit =
                        sineDepthLimit premiseSelectionParameters
                    , sinePremiseSelectionTolerance =
                        sineTolerance premiseSelectionParameters
                    , sinePremiseSelectionAxiomNumberLimit =
                        sinePremiseNumberLimit premiseSelectionParameters
                    }]
        case premiseSelectionResult of
          SineResult sineResult ->
            SInE.saveToDatabase opts sineResult omsEntity sinePremiseSelectionKey
          _ -> return ()

postprocessReasoning :: HetcatsOpts
                     -> ReasoningCacheGoal
                     -> Maybe [String]
                     -> ProofResult
                     -> IO ()
postprocessReasoning opts reasoningCacheGoal premisesM
  (_, goalResult, _, _, _, proofStatusM, consCheckerOutputM) =
  case rceReasoningAttemptKeyM reasoningCacheGoal of
    Nothing -> return ()
    Just reasoningAttemptKey -> onDatabase (databaseConfig opts) $ do
      Just reasoningAttemptValue <- get reasoningAttemptKey
      let reasoningAttemptEntity = Entity reasoningAttemptKey reasoningAttemptValue
      let reasonerKey = fromJust $ reasoningAttemptUsedReasonerId reasoningAttemptValue
      case rceProverMode reasoningCacheGoal of
        GlConsistency -> do
          let consistencyStatus_ = convertGoalResultConsistencyStatus goalResult
          omsEntity <- getOmsFromConsistencyCheckAttempt reasoningAttemptKey
          createReasonerOutput reasoningAttemptKey reasonerKey $
            fromJust consCheckerOutputM
          advisoryLocked opts (omsLockKey $ entityKey omsEntity) $ do
            finishReasoningAttempt reasoningAttemptEntity Nothing
            updateConsistencyCheckAttempt reasoningAttemptKey consistencyStatus_
            evaluationStates <- fetchOmsEvaluationStates omsEntity
            consistencyStatuses <- fetchConsistencyStatuses omsEntity
            setOmsEvaluationState omsEntity $
              chooseEvaluationState evaluationStates
            setOmsConsistencyCheckStatus omsEntity $
              chooseConsistencyStatus consistencyStatuses
        GlProofs -> do
          let proofStatus = fromJust proofStatusM
          let timeTakenM = Just $ convertTime $ LP.usedTime proofStatus
          createGeneratedAxioms reasoningAttemptKey proofStatus
          createReasonerOutput reasoningAttemptKey reasonerKey $
            unlines $ LP.proofLines proofStatus
          let proofStatusSZS = convertGoalResultProofStatus goalResult premisesM
          omsEntity <- getOmsFromProofAttempt reasoningAttemptKey
          usedSentencesIds <- getUsedSentencesIds omsEntity $
            fmap LP.usedAxioms proofStatusM
          conjectureEntity <- getConjectureFromReasoningAttempt reasoningAttemptKey
          advisoryLocked opts (conjectureLockKey $ entityKey conjectureEntity) $ do
            finishReasoningAttempt reasoningAttemptEntity timeTakenM
            updateProofAttempt reasoningAttemptKey proofStatusSZS usedSentencesIds
            evaluationStates <- fetchConjectureEvaluationStates conjectureEntity
            proofStatusesSZS <- fetchProofStatuses conjectureEntity
            setConjectureEvaluationState conjectureEntity $
              chooseEvaluationState evaluationStates
            setConjectureProofStatus conjectureEntity $
              chooseProofStatus proofStatusesSZS
      return ()
  where
    getOmsFromConsistencyCheckAttempt :: MonadIO m
                                      => DatabaseSchema.ReasoningAttemptId
                                      -> DBMonad m (Entity LocIdBase)
    getOmsFromConsistencyCheckAttempt reasoningAttemptKey = do
      omsL <- select $ from $
        \ (reasoning_attempts `InnerJoin` consistency_check_attempts
                              `InnerJoin` loc_id_bases) -> do
          on $ just (loc_id_bases ^. LocIdBaseId) ==.
                 consistency_check_attempts ^. ConsistencyCheckAttemptOmsId
          on $ consistency_check_attempts ^. ConsistencyCheckAttemptId ==.
                 coerceId (reasoning_attempts ^. ReasoningAttemptId)
          where_ $ reasoning_attempts ^. ReasoningAttemptId ==.
                     val reasoningAttemptKey
          limit 1
          return loc_id_bases
      case omsL of
        [] -> fail "Persistence.Reasoning.postprocessReasoning: could not find OMS"
        omsEntity : _ -> return omsEntity

    getOmsFromProofAttempt :: MonadIO m
                           => DatabaseSchema.ReasoningAttemptId
                           -> DBMonad m (Entity LocIdBase)
    getOmsFromProofAttempt reasoningAttemptKey = do
      omsL <- select $ from $
        \ (reasoning_attempts `InnerJoin` proof_attempts
                              `InnerJoin` sentences
                              `InnerJoin` loc_id_bases_oms) -> do
          on $ loc_id_bases_oms ^. LocIdBaseId ==.
                 (sentences ^. SentenceOmsId)
          on $ just (coerceId (sentences ^. SentenceId)) ==.
                 proof_attempts ^. ProofAttemptConjectureId
          on $ proof_attempts ^. ProofAttemptId ==.
                 coerceId (reasoning_attempts ^. ReasoningAttemptId)
          where_ $ reasoning_attempts ^. ReasoningAttemptId ==.
                     val reasoningAttemptKey
          limit 1
          return loc_id_bases_oms
      case omsL of
        [] -> fail "Persistence.Reasoning.postprocessReasoning: could not find OMS"
        omsEntity : _ -> return omsEntity

    getConjectureFromReasoningAttempt :: MonadIO m
                                      => DatabaseSchema.ReasoningAttemptId
                                      -> DBMonad m (Entity LocIdBase)
    getConjectureFromReasoningAttempt reasoningAttemptKey = do
      conjectureL <- select $ from $
        \ (reasoning_attempts `InnerJoin` proof_attempts
                              `InnerJoin` loc_id_bases) -> do
          on $ just (loc_id_bases ^. LocIdBaseId) ==.
                 proof_attempts ^. ProofAttemptConjectureId
          on $ proof_attempts ^. ProofAttemptId ==.
                 coerceId (reasoning_attempts ^. ReasoningAttemptId)
          where_ $ reasoning_attempts ^. ReasoningAttemptId ==.
                     val reasoningAttemptKey
          limit 1
          return loc_id_bases
      case conjectureL of
        [] -> fail "Persistence.Reasoning.postprocessReasoning: could not find Conjecture"
        conjectureEntity : _ -> return conjectureEntity

    getUsedSentencesIds :: MonadIO m
                        => Entity LocIdBase
                        -> Maybe [String]
                        -> DBMonad m [LocIdBaseId] -- Sentence IDs
    getUsedSentencesIds omsEntity sentenceNamesM =
      case sentenceNamesM of
        Nothing -> return []
        Just sentenceNames ->
          let sentenceLocIds = map (locIdOfSentence omsEntity) sentenceNames
          in  do
                sentences <- select $ from $ \ loc_id_bases -> do
                  where_ $ loc_id_bases ^. LocIdBaseLocId `in_` valList sentenceLocIds
                  return loc_id_bases
                return $ map (\ (Entity sentenceKey _) -> sentenceKey) sentences

    finishReasoningAttempt :: MonadIO m
                           => Entity DatabaseSchema.ReasoningAttempt
                           -> Maybe Int
                           -> DBMonad m ()
    finishReasoningAttempt (Entity reasoningAttemptKey reasoningAttemptValue) timeTakenM = do
        update (reasoningAttemptActionId reasoningAttemptValue)
               [ ActionEvaluationState =. EvaluationStateType.FinishedSuccessfully
               , ActionMessage =. Nothing
               ]
        update reasoningAttemptKey [ReasoningAttemptTimeTaken =. timeTakenM]
        return ()

    updateConsistencyCheckAttempt :: MonadIO m
                                  => DatabaseSchema.ReasoningAttemptId
                                  -> ConsistencyStatusType.ConsistencyStatusType
                                  -> DBMonad m ()
    updateConsistencyCheckAttempt reasoningAttemptKey consistencyStatus_ =
      update (toSqlKey $ fromSqlKey reasoningAttemptKey :: DatabaseSchema.ConsistencyCheckAttemptId)
             [ ConsistencyCheckAttemptConsistencyStatus =. consistencyStatus_
             ]

    updateProofAttempt :: MonadIO m
                       => DatabaseSchema.ReasoningAttemptId
                       -> Enums.ProofStatusType
                       -> [LocIdBaseId]
                       -> DBMonad m ()
    updateProofAttempt reasoningAttemptKey proofStatus usedSentencesIds = do
      update (toSqlKey $ fromSqlKey reasoningAttemptKey)
             [ ProofAttemptProofStatus =. proofStatus
             ]
      mapM_ (\ sentenceKey -> insert ProofAttemptUsedSentence
              { proofAttemptUsedSentenceProofAttemptId =
                  toSqlKey $ fromSqlKey reasoningAttemptKey
              , proofAttemptUsedSentenceSentenceId = sentenceKey
              }
            ) usedSentencesIds

fetchOmsEvaluationStates :: MonadIO m
                         => Entity DatabaseSchema.LocIdBase
                         -> DBMonad m [EvaluationStateType.EvaluationStateType]
fetchOmsEvaluationStates (Entity omsKey _) = do
  actions <- select $ from $ \ (actions `InnerJoin` reasoning_attempts
                                        `InnerJoin` consistency_check_attempts
                                        `InnerJoin` loc_id_bases) -> do
    on $ coerceId(loc_id_bases ^. LocIdBaseId) ==.
           consistency_check_attempts ^. ConsistencyCheckAttemptOmsId
    on $ coerceId (consistency_check_attempts ^. ConsistencyCheckAttemptId) ==.
           reasoning_attempts ^. ReasoningAttemptId
    on $ reasoning_attempts ^. ReasoningAttemptActionId ==.
           actions ^. ActionId
    where_ $ loc_id_bases ^. LocIdBaseId ==. val omsKey
    return actions
  return $ map (\ (Entity _ actionValue) ->
                 actionEvaluationState actionValue
               ) actions

fetchConsistencyStatuses :: MonadIO m
                         => Entity DatabaseSchema.LocIdBase
                         -> DBMonad m [ConsistencyStatusType.ConsistencyStatusType]
fetchConsistencyStatuses (Entity omsKey _) = do
  consistencyCheckAttempts <- select $ from $ \ consistency_check_attempts -> do
    where_ $ consistency_check_attempts ^. ConsistencyCheckAttemptOmsId ==.
               just (val omsKey)
    return consistency_check_attempts
  return $ map (\ (Entity _ consistencyCheckAttemptValue) ->
                 consistencyCheckAttemptConsistencyStatus consistencyCheckAttemptValue
               ) consistencyCheckAttempts

fetchProofStatuses :: MonadIO m
                   => Entity DatabaseSchema.LocIdBase
                   -> DBMonad m [Enums.ProofStatusType]
fetchProofStatuses (Entity conjectureKey _) = do
  proofAttempts <- select $ from $ \ proof_attempts -> do
    where_ $ proof_attempts ^. ProofAttemptConjectureId ==. just (val conjectureKey)
    return proof_attempts
  return $ map (\ (Entity _ proofAttemptValue) ->
                 proofAttemptProofStatus proofAttemptValue
               ) proofAttempts

fetchConjectureEvaluationStates :: MonadIO m
                                => Entity DatabaseSchema.LocIdBase
                                -> DBMonad m [EvaluationStateType.EvaluationStateType]
fetchConjectureEvaluationStates (Entity conjectureKey _) = do
  actions <- select $ from $ \ (actions `InnerJoin` reasoning_attempts
                                        `InnerJoin` proof_attempts
                                        `InnerJoin` loc_id_bases) -> do
    on $ coerceId(loc_id_bases ^. LocIdBaseId) ==.
           proof_attempts ^. ProofAttemptConjectureId
    on $ coerceId (proof_attempts ^. ProofAttemptId) ==.
           reasoning_attempts ^. ReasoningAttemptId
    on $ reasoning_attempts ^. ReasoningAttemptActionId ==.
           actions ^. ActionId
    where_ $ loc_id_bases ^. LocIdBaseId ==. val conjectureKey
    return actions
  return $ map (\ (Entity _ actionValue) ->
                 actionEvaluationState actionValue
               ) actions

chooseEvaluationState :: [EvaluationStateType.EvaluationStateType]
                      -> EvaluationStateType.EvaluationStateType
chooseEvaluationState =
  let ordering = [ EvaluationStateType.FinishedUnsuccessfully
                 , EvaluationStateType.FinishedSuccessfully
                 , EvaluationStateType.NotYetEnqueued
                 , EvaluationStateType.Enqueued
                 , EvaluationStateType.Processing
                 ]
  in  maximumBy (\ a b -> compare (elemIndex a ordering) (elemIndex b ordering))

chooseConsistencyStatus :: [ConsistencyStatusType.ConsistencyStatusType]
                        -> ConsistencyStatusType.ConsistencyStatusType
chooseConsistencyStatus statuses =
  if ConsistencyStatusType.Consistent `elem` statuses &&
       ConsistencyStatusType.Inconsistent `elem` statuses
  then ConsistencyStatusType.Contradictory
  else let ordering = [ ConsistencyStatusType.Open
                      , ConsistencyStatusType.Timeout
                      , ConsistencyStatusType.Error
                      , ConsistencyStatusType.Inconsistent
                      , ConsistencyStatusType.Consistent
                      , ConsistencyStatusType.Contradictory
                      ]
           fixOrdering a b =
             compare (elemIndex a ordering) (elemIndex b ordering)
       in  maximumBy fixOrdering statuses

chooseProofStatus :: [Enums.ProofStatusType] -> Enums.ProofStatusType
chooseProofStatus statuses =
  if Enums.THM `elem` statuses && Enums.CSA `elem` statuses
  then Enums.CONTR
  else let ordering = [ Enums.OPN
                      , Enums.UNK
                      , Enums.RSO
                      , Enums.ERR
                      , Enums.CSAS
                      , Enums.CSA
                      , Enums.THM
                      , Enums.CONTR
                      ]
           fixOrdering a b =
             compare (elemIndex a ordering) (elemIndex b ordering)
       in  maximumBy fixOrdering statuses

setOmsEvaluationState :: MonadIO m
                      => Entity DatabaseSchema.LocIdBase
                      -> EvaluationStateType.EvaluationStateType
                      -> DBMonad m ()
setOmsEvaluationState (Entity omsKey _) evaluationState = do
  actionL <- select $ from $ \ (actions `InnerJoin` oms) -> do
    on $ actions ^. ActionId ==. oms ^. OMSActionId
    where_ $ oms ^. OMSId ==. val (toSqlKey $ fromSqlKey omsKey)
    limit 1
    return actions
  (Entity actionKey _) <- case actionL of
    [] -> fail "Persistence.Reasoning.setOmsEvaluationState: Could not find Action"
    actionEntity : _ -> return actionEntity
  update actionKey [ActionEvaluationState =. evaluationState]
  return ()

setConjectureEvaluationState :: MonadIO m
                             => Entity DatabaseSchema.LocIdBase
                             -> EvaluationStateType.EvaluationStateType
                             -> DBMonad m ()
setConjectureEvaluationState (Entity conjectureKey _) evaluationState = do
  actionL <- select $ from $ \ (actions `InnerJoin` conjectures) -> do
    on $ actions ^. ActionId ==. conjectures ^. ConjectureActionId
    where_ $ conjectures ^. ConjectureId ==. val (toSqlKey $ fromSqlKey conjectureKey)
    limit 1
    return actions
  (Entity actionKey _) <- case actionL of
    [] -> fail "Persistence.Reasoning.setConjectureEvaluationState: Could not find Action"
    actionEntity : _ -> return actionEntity
  update actionKey [ActionEvaluationState =. evaluationState]
  return ()

setOmsConsistencyCheckStatus :: MonadIO m
                             => Entity DatabaseSchema.LocIdBase
                             -> ConsistencyStatusType.ConsistencyStatusType
                             -> DBMonad m ()
setOmsConsistencyCheckStatus (Entity omsKey _) consistencyCheckStatus = do
  E.update $ \ oms -> do
    set oms [OMSConsistencyStatus E.=. val consistencyCheckStatus]
    where_ $ coerceId (oms ^. OMSId) ==. val omsKey
  return ()

setConjectureProofStatus :: MonadIO m
                         => Entity DatabaseSchema.LocIdBase
                         -> Enums.ProofStatusType
                         -> DBMonad m ()
setConjectureProofStatus (Entity conjectureKey _) proofStatus = do
  E.update $ \ conjectures -> do
    set conjectures [ ConjectureProofStatus E.=. val proofStatus]
    where_ $ coerceId (conjectures ^. ConjectureId) ==. val conjectureKey
  return ()

findDocument :: MonadIO m
             => HetcatsOpts -> String -> DBMonad m (Entity LocIdBase)
findDocument opts location = do
  let locId = locIdOfDocument opts (Just location) ""
  findLocIdBase "Document" [Enums.Library, Enums.NativeDocument] locId

findOMS :: MonadIO m
        => Entity LocIdBase
        -> DGNodeLab
        -> DBMonad m (Entity LocIdBase)
findOMS documentEntity nodeLabel = do
  let locId = locIdOfOMS documentEntity nodeLabel
  findLocIdBase "OMS" [Enums.OMS] locId

findConjecture :: MonadIO m
               => Entity LocIdBase
               -> String
               -> DBMonad m (Entity LocIdBase)
findConjecture omsEntity name = do
  let locId = locIdOfSentence omsEntity name
  findLocIdBase "Conjecture" [ Enums.OpenConjecture
                             , Enums.Theorem
                             , Enums.CounterTheorem
                             ] locId

findPremise :: MonadIO m
            => Entity LocIdBase
            -> String
            -> DBMonad m (Entity LocIdBase)
findPremise omsEntity name = do
  let locId = locIdOfSentence omsEntity name
  findLocIdBase "Premise" [ Enums.OpenConjecture
                          , Enums.Theorem
                          , Enums.CounterTheorem
                          , Enums.Axiom
                          ] locId

createGeneratedAxioms :: MonadIO m
                      => ReasoningAttemptId
                      -> LP.ProofStatus G_proof_tree
                      -> DBMonad m ()
createGeneratedAxioms reasoningAttemptKey proofStatus =
  mapM_ (\ axiomText -> insert GeneratedAxiom
          { generatedAxiomReasoningAttemptId = reasoningAttemptKey
          , generatedAxiomText = Text.pack axiomText
          }
        ) $ LP.usedAxioms proofStatus

createReasonerOutput :: MonadIO m
                     => ReasoningAttemptId
                     -> ReasonerId
                     -> String
                     -> DBMonad m ReasonerOutputId
createReasonerOutput reasoningAttemptKey reasonerKey text =
  insert ReasonerOutput
    { reasonerOutputReasoningAttemptId = reasoningAttemptKey
    , reasonerOutputReasonerId = reasonerKey
    , reasonerOutputText = Text.pack text
    }

findLocIdBase :: MonadIO m
              => String
              -> [Enums.LocIdBaseKindType]
              -> String
              -> DBMonad m (Entity LocIdBase)
findLocIdBase entityKind kinds locId = do
  omsL <-
    select $ from $ \ loc_id_bases -> do
      where_ (loc_id_bases ^. LocIdBaseLocId ==. val locId &&. loc_id_bases ^. LocIdBaseKind `in_` valList kinds)
      return loc_id_bases
  case omsL of
    [] -> fail ("Could not save reasoning results to database: " ++ entityKind ++ " not found in database.")
    entity : _ -> return entity

convertTime :: TimeOfDay -> Int
convertTime tod =
  -- Sometimes, the reasoning system returns -1 seconds
  maximum [ floor (read $ init $ show $ timeOfDayToTime tod :: Double)
          , 0
          ]

convertGoalResultConsistencyStatus :: String
                                   -> ConsistencyStatusType.ConsistencyStatusType
convertGoalResultConsistencyStatus goalResult
  | "Timeout" `isPrefixOf` goalResult = ConsistencyStatusType.Timeout
  | "Error" `isPrefixOf` goalResult = ConsistencyStatusType.Timeout
  | "Consistent" `isPrefixOf` goalResult = ConsistencyStatusType.Consistent
  | "Inconsistent" `isPrefixOf` goalResult = ConsistencyStatusType.Inconsistent
  | otherwise = ConsistencyStatusType.Open

convertGoalResultProofStatus :: String -> Maybe [String] -> Enums.ProofStatusType
convertGoalResultProofStatus goalResult premisesM
  | "Proved" `isPrefixOf` goalResult = Enums.THM
  | "Disproved" `isPrefixOf` goalResult && Maybe.isNothing premisesM = Enums.CSA
  | "Disproved" `isPrefixOf` goalResult && premisesM == Just [] = Enums.CSA
  | "Disproved" `isPrefixOf` goalResult && premisesM /= Just [] = Enums.CSAS
  | "Timeout" `isInfixOf` goalResult = Enums.RSO
  | otherwise = Enums.UNK

conjectureLockKey :: DatabaseSchema.LocIdBaseId -> String
conjectureLockKey conjectureKey =
  "conjecture-reasoning-" ++ show (fromSqlKey conjectureKey)

omsLockKey :: DatabaseSchema.LocIdBaseId -> String
omsLockKey omsKey =
  "oms-reasoning-" ++ show (fromSqlKey omsKey)
