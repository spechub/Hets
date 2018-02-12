{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TypeFamilies               #-}

module Persistence.Reasoning ( setupReasoning
                             , preprocessReasoning
                             , postprocessReasoning
                             ) where
import Debug.Trace

import Persistence.Database
import Persistence.DevGraph.Cleaning
import Persistence.Diagnosis
import Persistence.FileVersion
import Persistence.LogicGraph
import Persistence.Schema as DatabaseSchema
import Persistence.Schema.MappingOrigin (MappingOrigin)
import qualified Persistence.Schema.MappingOrigin as MappingOrigin
import Persistence.Range
import Persistence.Schema.MappingType (MappingType)
import qualified Persistence.Schema.Enums as Enums
import qualified Persistence.Schema.EvaluationStateType as EvaluationStateType
import qualified Persistence.Schema.MappingType as MappingType
import Persistence.Schema.OMSOrigin (OMSOrigin)
import qualified Persistence.Schema.OMSOrigin as OMSOrigin
import qualified Persistence.Schema.ReasoningStatusOnReasoningAttemptType as ReasoningStatusOnReasoningAttemptType
import qualified Persistence.Schema.ReasoningStatusOnConjectureType as ReasoningStatusOnConjectureType
import Persistence.Utils

import Persistence.Reasoning.PremiseSelectionSInE as SInE
import PGIP.ReasoningParameters as ReasoningParameters

import Common.LibName
import Driver.Options
import Interfaces.GenericATPState (tsTimeLimit, tsExtraOpts)
import Logic.Comorphism (AnyComorphism)
import Logic.Grothendieck
import qualified Logic.Prover as LP
import Proofs.AbstractState (G_proof_tree, G_prover (..), ProverOrConsChecker (..), getProverName, getCcName)
import Static.DevGraph
import Static.GTheory

import Control.Exception (catch)
import Control.Exception.Base (SomeException)
import Control.Monad (when)
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.Trans.Class (lift)
import Data.Char (toLower)
import Data.Data
import Data.Maybe (isJust, fromJust, fromMaybe)
import Data.List (isPrefixOf, isInfixOf)
import qualified Data.Text as Text
import Data.Time.LocalTime
import Database.Persist hiding ((==.))
import Database.Persist.Sql hiding ((==.))
import Database.Esqueleto hiding ((=.), update)
import Numeric
import Text.Printf (printf)

type ProofResult = (String, String, String, ProverOrConsChecker,
                -- (goalName, goalResult, goalDetails, prover,
                    AnyComorphism, Maybe (LP.ProofStatus G_proof_tree))
                -- comorphism, proofStatusM)

setupReasoning :: HetcatsOpts
               -> String
               -> Maybe ReasoningParameters
               -> Bool
               -> IO (Maybe ReasonerConfigurationId)
setupReasoning opts location reasoningParametersM doUseDatabase
  | doUseDatabase = case reasoningParametersM of
      Just reasoningParameters ->
        onDatabase (databaseConfig opts) $
          fmap Just $ createReasonerConfiguration reasoningParameters
      Nothing -> return Nothing
  | otherwise = return Nothing

createReasonerConfiguration :: MonadIO m
                            => ReasoningParameters
                            -> DBMonad m ReasonerConfigurationId
createReasonerConfiguration reasoningParameters = do
  reasonerEntityM <- case reasoner $ reasonerConfiguration reasoningParameters of
    Nothing -> return Nothing
    Just reasonerName -> findReasoner reasonerName Enums.Prover
  let reasonerKeyM = fmap (\ (Entity key _) -> key) reasonerEntityM
  insert DatabaseSchema.ReasonerConfiguration
    { reasonerConfigurationConfiguredReasonerId = reasonerKeyM
    , reasonerConfigurationTimeLimit =
        Just $ timeLimit $ reasonerConfiguration reasoningParameters
    }

preprocessReasoning :: HetcatsOpts
                    -> LibEnv
                    -> LibName
                    -> DGraph
                    -> (Int, DGNodeLab)
                    -> G_theory
                    -> G_sublogics
                    -> String
                    -> String
                    -> String
                    -> Maybe ReasoningParameters
                    -> Maybe ReasonerConfigurationId
                    -> G_prover
                    -> AnyComorphism
                    -> IO (Maybe [String], Maybe ReasoningAttemptId)
preprocessReasoning opts libEnv libName dGraph nodeLabel gTheory gSublogics location nodeName goalName reasoningParametersM reasonerConfigurationKeyM prover comorphism = trace ("preprocessReasoning.reasonerConfigurationKeyM: " ++ show reasonerConfigurationKeyM) $
  case reasoningParametersM of
    Nothing -> return (Nothing, Nothing)
    Just reasoningParameters ->
      case premiseSelection reasoningParameters of
        Nothing -> return (Nothing, Nothing)
        Just premiseSelectionParameters -> do
          let premiseSelectionKindV = case map toLower $ kind premiseSelectionParameters of
                "sine" -> Enums.SinePremiseSelection
                _ -> Enums.ManualPremiseSelection
          premiseSelectionResultData@(premisesM, _, _) <-
            performPremiseSelection opts libEnv libName dGraph nodeLabel gTheory
              gSublogics goalName premiseSelectionParameters premiseSelectionKindV
          case reasonerConfigurationKeyM of
              Nothing -> return (premisesM, Nothing)
              Just reasonerConfigurationKey -> onDatabase (databaseConfig opts) $ do
                (reasoningAttemptEntity@(Entity reasoningAttemptKey _), omsEntity) <-
                  createProofAttempt opts location nodeName goalName
                    reasonerConfigurationKey prover comorphism
                createPremiseSelection opts location nodeName goalName
                  reasoningAttemptEntity premiseSelectionParameters
                  premiseSelectionKindV premiseSelectionResultData omsEntity
                trace ("preprocessReasoning.premisesM: " ++ show premisesM) $ return (premisesM, Just reasoningAttemptKey)
                trace ("preprocessReasoning.reasoningAttemptKey: " ++ show reasoningAttemptKey) $ return (premisesM, Just reasoningAttemptKey)
                return (premisesM, Just reasoningAttemptKey)

data PremiseSelectionResultForDatabase = NoResult
                                       | SineResult SInE.SInEResult

performPremiseSelection :: HetcatsOpts
                        -> LibEnv
                        -> LibName
                        -> DGraph
                        -> (Int, DGNodeLab)
                        -> G_theory
                        -> G_sublogics
                        -> String
                        -> ReasoningParameters.PremiseSelection
                        -> Enums.PremiseSelectionKindType
                        -> IO (Maybe [String], Int, PremiseSelectionResultForDatabase)
performPremiseSelection opts libEnv libName dGraph nodeLabel gTheory gSublogics goalName premiseSelectionParameters premiseSelectionKindV =
  case premiseSelectionKindV of
    Enums.ManualPremiseSelection ->
      return (manualPremises premiseSelectionParameters, 0, NoResult)
    Enums.SinePremiseSelection -> do
      (premisesM, timeTaken, sineResult) <-
        SInE.perform opts libEnv libName dGraph nodeLabel gTheory gSublogics
          goalName premiseSelectionParameters
      return (premisesM, timeTaken, SineResult sineResult)

createProofAttempt :: MonadIO m
                   => HetcatsOpts
                   -> String
                   -> String
                   -> String
                   -> ReasonerConfigurationId
                   -> G_prover
                   -> AnyComorphism
                   -> DBMonad m (Entity ReasoningAttempt, Entity LocIdBase)
createProofAttempt opts location nodeName goalName reasonerConfigurationKey prover comorphism = do
  documentEntity <- findDocument opts location
  omsEntity <- findOMS documentEntity nodeName
  (Entity reasonerKey _) <- findReasonerByGProver prover
  logicTranslationEntityM <- findOrCreateLogicTranslation opts comorphism
  conjectureKeyOrError <- liftIO $ Control.Exception.catch
    (do
      Entity conjectureKey _ <- onDatabase (databaseConfig opts) $
        findConjecture omsEntity goalName
      return $ Right conjectureKey
    )
    (\ exception ->
      return $ Left ("Persistence.Reasoning.createProofAttempt: Could not find conjecture \"" ++ goalName ++ "\" - " ++ show (exception :: SomeException))
    )
  case conjectureKeyOrError of
    Right conjectureKey -> do
      reasoningAttemptEntity@(Entity reasoningAttemptKey _) <-
        insertReasoningAttempt EvaluationStateType.Processing
                               Nothing
                               ReasoningStatusOnReasoningAttemptType.OPN
                               (Just reasonerKey)
                               (fmap entityKey logicTranslationEntityM)
      let proofAttemptKey = toSqlKey $ fromSqlKey reasoningAttemptKey
      let proofAttemptValue = DatabaseSchema.ProofAttempt
            { proofAttemptConjectureId = Just conjectureKey }
      insertEntityMany [Entity proofAttemptKey proofAttemptValue]
      return (reasoningAttemptEntity, omsEntity)
    Left message -> do
      insertReasoningAttempt EvaluationStateType.FinishedUnsuccessfully
                             (Just $ Text.pack message)
                             ReasoningStatusOnReasoningAttemptType.ERR
                             (Just reasonerKey)
                             (fmap entityKey logicTranslationEntityM)
      fail message
  where
    insertReasoningAttempt evaluationState messageM reasoningStatus reasonerKey
      logicTranslationKey = do
      actionKey <- insert Action
        { actionEvaluationState = evaluationState
        , actionMessage = messageM
        }
      let reasoningAttemptValue = DatabaseSchema.ReasoningAttempt
            { reasoningAttemptActionId = actionKey
            , reasoningAttemptReasonerConfigurationId = reasonerConfigurationKey
            , reasoningAttemptUsedReasonerId = reasonerKey
            , reasoningAttemptUsedLogicTranslationId = logicTranslationKey
            , reasoningAttemptTimeTaken = Nothing
            , reasoningAttemptReasoningStatus = reasoningStatus
            }
      reasoningAttemptKey <- insert reasoningAttemptValue
      return (Entity reasoningAttemptKey reasoningAttemptValue)

createPremiseSelection :: MonadIO m
                       => HetcatsOpts
                       -> String
                       -> String
                       -> String
                       -> Entity ReasoningAttempt
                       -> ReasoningParameters.PremiseSelection
                       -> Enums.PremiseSelectionKindType
                       -> (Maybe [String], Int, PremiseSelectionResultForDatabase)
                       -> Entity LocIdBase
                       -> DBMonad m ()
createPremiseSelection opts location nodeName goalName
  (Entity reasoningAttemptKey reasoningAttemptValue)
  premiseSelectionParameters premiseSelectionKindV
  (premisesM, timeTaken, premiseSelectionResult) omsEntity = do
  let premises = fromMaybe [] premisesM
  let proofAttemptKey = toSqlKey $ fromSqlKey reasoningAttemptKey
  let premiseSelectionValue = DatabaseSchema.PremiseSelection
        { premiseSelectionReasonerConfigurationId = reasoningAttemptReasonerConfigurationId reasoningAttemptValue
        , premiseSelectionProofAttemptId = proofAttemptKey
        , premiseSelectionKind = premiseSelectionKindV
        , premiseSelectionTimeTaken = Just timeTaken
        }
  premiseSelectionKey <- insert premiseSelectionValue
  createSpecificPremiseSelection premiseSelectionKey
  mapM_ (\ premiseName -> do
          premiseKeyM <- liftIO $ Control.Exception.catch
            (do
              premiseKey <- onDatabase (databaseConfig opts) $ findPremise omsEntity premiseName
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
        insertEntityMany [Entity (toSqlKey $ fromSqlKey premiseSelectionKey) DatabaseSchema.ManualPremiseSelection]
      Enums.SinePremiseSelection -> do
        let sinePremiseSelectionKey = toSqlKey $ fromSqlKey premiseSelectionKey
        insertEntityMany [Entity sinePremiseSelectionKey DatabaseSchema.SinePremiseSelection
          { sinePremiseSelectionDepthLimit = sineDepthLimit premiseSelectionParameters
          , sinePremiseSelectionTolerance = sineTolerance premiseSelectionParameters
          , sinePremiseSelectionAxiomNumberLimit = sinePremiseNumberLimit premiseSelectionParameters
          }]
        case premiseSelectionResultData of
          SineResult sineResult -> SInE.saveToDatabase opts sineResult sinePremiseSelectionKey
          _ -> return ()

postprocessReasoning :: HetcatsOpts
                     -> ProofResult
                     -> Maybe DatabaseSchema.ReasoningAttemptId
                     -> IO ()
postprocessReasoning opts _ Nothing = trace "postprocessReasoning.1" $ return ()
postprocessReasoning opts
  proofResult@(goalName, goalResult, goalDetails, proverOrConsChecker,
               comorphism, proofStatusM)
  (Just reasoningAttemptKey) = trace ("postprocessReasoning.proofResult: " ++ show proofResult) $ trace ("postprocessReasoning.reasoningAttemptKey: " ++ show reasoningAttemptKey) $
  onDatabase (databaseConfig opts) $ do
    Just reasoningAttemptValue <- get reasoningAttemptKey
    let reasonerKey = fromJust $ reasoningAttemptUsedReasonerId reasoningAttemptValue
    let proofStatus = fromJust proofStatusM
    let reasoningStatus = convertGoalResult goalResult
    let timeTaken = Just $ convertTime $ LP.usedTime proofStatus
    createGeneratedAxioms reasoningAttemptKey proofStatus
    createReasonerOutput reasoningAttemptKey reasonerKey proofStatus
    update (reasoningAttemptActionId reasoningAttemptValue)
           [ ActionEvaluationState =. EvaluationStateType.FinishedSuccessfully
           , ActionMessage =. Nothing
           ]
    update reasoningAttemptKey
           [ ReasoningAttemptReasoningStatus =. reasoningStatus
           , ReasoningAttemptTimeTaken =. timeTaken
           ]
    return ()

findDocument :: MonadIO m
             => HetcatsOpts -> String -> DBMonad m (Entity LocIdBase)
findDocument opts location = do
  trace ("findDocument: " ++ location) $ return ()
  let locId = locIdOfDocument opts (Just location) ""
  trace ("searching for document with locId: " ++ locId) $ return ()
  findLocIdBase "Document" [Enums.Library, Enums.NativeDocument] locId

findOMS :: MonadIO m
        => Entity LocIdBase
        -> String
        -> DBMonad m (Entity LocIdBase)
findOMS documentEntity nodeName = do
  trace ("DocumentValue: " ++ show (entityVal documentEntity)) $ return ()
  let locId = locIdOfOMS documentEntity nodeName
  trace ("searching for OMS with locId: " ++ locId) $ return ()
  findLocIdBase "OMS" [Enums.OMS] locId

findConjecture :: MonadIO m
               => Entity LocIdBase
               -> String
               -> DBMonad m (Entity LocIdBase)
findConjecture omsEntity name = do
  let locId = locIdOfSentence omsEntity name
  trace ("searching for Conjecture with locId: " ++ locId) $ return ()
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
  trace ("searching for Premise with locId: " ++ locId) $ return ()
  findLocIdBase "Premise" [ Enums.OpenConjecture
                          , Enums.Theorem
                          , Enums.CounterTheorem
                          , Enums.Axiom
                          ] locId

-- exportNodeReslults :: MonadIO m
--                    => HetcatsOpts
--                    -> Entity LocIdBase
--                    -> ReasonerConfigurationId
--                    -> (String, [ProofResult])
--                    -> DBMonad m ()
-- exportNodeReslults opts documentEntity reasonerConfigurationKey (nodeName, proofResults) = do
--   omsEntity <- findOMS documentEntity nodeName
--   trace ("found oms: " ++ show (fromIntegral $ fromSqlKey $ entityKey omsEntity)) $ return ()
--   mapM_ (exportGoalResult opts documentEntity omsEntity reasonerConfigurationKey) proofResults
--   return ()

-- exportGoalResult :: MonadIO m
--                  => HetcatsOpts
--                  -> Entity LocIdBase
--                  -> Entity LocIdBase
--                  -> ReasonerConfigurationId
--                  -> ProofResult
--                  -> DBMonad m ()
-- exportGoalResult opts documentEntity omsEntity reasonerConfigurationKey
--   (goalName, goalResult, goalDetails, proverOrConsChecker, comorphism, proofStatusM) = do
--   conjectureEntity <- findConjecture omsEntity goalName
--   trace ("found conjecture: " ++ show (fromIntegral $ fromSqlKey $ entityKey omsEntity)) $ return ()
--   -- Should always be "Just" at this point
--   when (isJust proofStatusM) $ do
--     let proofStatus = fromJust proofStatusM
--     reasonerKey <- findOrCreateProverOrConsChecker proverOrConsChecker
--     (_, logicMappingKey) <- findOrCreateLanguageMappingAndLogicMapping opts comorphism
--     actionKey <- insert Action
--       { actionEvaluationState = EvaluationStateType.FinishedSuccessfully
--       , actionMessage = Nothing
--       }
--     reasoningAttemptKey <- insert ReasoningAttempt
--       { reasoningAttemptActionId = actionKey
--       , reasoningAttemptReasonerConfigurationId = reasonerConfigurationKey
--       , reasoningAttemptUsedReasonerId = Just reasonerKey
--       , reasoningAttemptUsedLogicTranslationId = Just logicTranslationKey
--       , reasoningAttemptTimeTaken = Just $ convertTime $ LP.usedTime proofStatus
--       , reasoningAttemptReasoningStatus = convertGoalResult goalResult
--       }
--     let proofAttempt = ProofAttempt
--           { proofAttemptConjectureId = Just $ toSqlKey $ fromSqlKey $ entityKey conjectureEntity }
--     insertEntityMany [Entity (toSqlKey $ fromSqlKey reasoningAttemptKey) proofAttempt]
--     createGeneratedAxioms reasoningAttemptKey proofStatus
--     createReasonerOutput reasoningAttemptKey reasonerKey proofStatus
--     return ()
--   return ()

-- findOrCreateProverOrConsChecker :: MonadIO m
--                                 => ProverOrConsChecker -> DBMonad m ReasonerId
-- findOrCreateProverOrConsChecker proverOrConsChecker = case proverOrConsChecker of
--   Prover gProver -> findOrCreateProver gProver
--   ConsChecker gConsistencyChecker -> findOrCreateConsistencyChecker gConsistencyChecker

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
                     -> LP.ProofStatus G_proof_tree
                     -> DBMonad m ReasonerOutputId
createReasonerOutput reasoningAttemptKey reasonerKey proofStatus =
  insert ReasonerOutput
    { reasonerOutputReasoningAttemptId = reasoningAttemptKey
    , reasonerOutputReasonerId = reasonerKey
    , reasonerOutputText = Text.pack $ unlines $ LP.proofLines proofStatus
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
convertTime tod = floor (read $ init $ show $ timeOfDayToTime tod :: Double)

convertGoalResult :: String -> ReasoningStatusOnReasoningAttemptType.ReasoningStatusOnReasoningAttemptType
convertGoalResult goalResult
  | "Proved" `isPrefixOf` goalResult = ReasoningStatusOnReasoningAttemptType.THM
  | "Disproved" `isPrefixOf` goalResult = ReasoningStatusOnReasoningAttemptType.CSA
  | "Timeout" `isInfixOf` goalResult = ReasoningStatusOnReasoningAttemptType.RSO
  | otherwise = ReasoningStatusOnReasoningAttemptType.UNK
