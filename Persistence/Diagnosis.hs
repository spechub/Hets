{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeFamilies               #-}

{- |
Module      :  Persistence.Diagnosis.hs
Copyright   :  (c) Uni Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  portable
-}

module Persistence.Diagnosis (saveDiagnoses) where

import Persistence.Database
import Persistence.DBConfig
import Persistence.FileVersion
import qualified Persistence.Schema.Enums as Enums
import qualified Persistence.Schema.EvaluationStateType as EvaluationStateType
import Persistence.Range
import Persistence.Schema as SchemaClass

import qualified Common.Result as Result

import Control.Monad.IO.Class (MonadIO (..))
import qualified Data.Text as Text
import Database.Persist

saveDiagnoses :: DBConfig -> DBContext -> Int -> [Result.Diagnosis] -> IO ()
saveDiagnoses dbConfig dbContext verbosity diagnoses =
  onDatabase dbConfig $ do
    (Entity fileVersionKey _) <- getFileVersion dbContext
    mapM_ (saveDiagnosis fileVersionKey) $
      Result.filterDiags verbosity diagnoses
    let errors = filter ((Result.Error ==) . Result.diagKind) diagnoses
    let state = if null errors
                then EvaluationStateType.FinishedSuccessfully
                else EvaluationStateType.FinishedUnsuccessfully
    setFileVersionStateOn fileVersionKey state

saveDiagnosis :: MonadIO m
              => FileVersionId -> Result.Diagnosis -> DBMonad m ()
saveDiagnosis fileVersionKey diagnosis =
    let kind = case Result.diagKind diagnosis of
          Result.Error -> Enums.Error
          Result.Warning -> Enums.Warn
          Result.Hint -> Enums.Hint
          _ -> Enums.Debug
        text = Result.diagString diagnosis
        range = Result.diagPos diagnosis
    in do
         rangeKeyM <- createRange range
         insert SchemaClass.Diagnosis
           { diagnosisFileVersionId = fileVersionKey
           , diagnosisKind = kind
           , diagnosisText = Text.pack text
           , diagnosisFileRangeId = rangeKeyM
           }
         return ()
