{-# LANGUAGE TemplateHaskell #-}
module Persistence.Schema.EvaluationStateType where

import Data.List (isPrefixOf)
import Database.Persist.TH

data EvaluationStateType = NotYetEnqueued
                         | Enqueued
                         | Processing
                         | FinishedSuccessfully
                         | FinishedUnsuccessfully
                           deriving (Eq)

instance Show EvaluationStateType where
  show NotYetEnqueued = "not_yet_enqueued"
  show Enqueued = "enqueued"
  show Processing = "processing"
  show FinishedSuccessfully = "finished_successfully"
  show FinishedUnsuccessfully = "finished_unsuccessfully"

instance Read EvaluationStateType where
  readsPrec _ input
    | show NotYetEnqueued `isPrefixOf` input = [(NotYetEnqueued, drop (length $ show NotYetEnqueued) input)]
    | show Enqueued `isPrefixOf` input = [(Enqueued, drop (length $ show Enqueued) input)]
    | show Processing `isPrefixOf` input = [(Processing, drop (length $ show Processing) input)]
    | show FinishedSuccessfully `isPrefixOf` input = [(FinishedSuccessfully, drop (length $ show FinishedSuccessfully) input)]
    | show FinishedUnsuccessfully `isPrefixOf` input = [(FinishedUnsuccessfully, drop (length $ show FinishedUnsuccessfully) input)]
    | otherwise = []

derivePersistField "EvaluationStateType"
