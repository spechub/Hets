{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
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
import Persistence.Range
import Persistence.Schema as SchemaClass

import qualified Common.Result as Result

import Control.Monad (foldM_)
import Control.Monad.IO.Class (MonadIO (..))
import qualified Data.Text as Text
import Database.Persist

saveDiagnoses :: DBConfig -> Int -> [Result.Diagnosis] -> IO ()
saveDiagnoses dbConfig verbosity diagnoses =
  onDatabase dbConfig $ do
    -- TODO: find the correct Repository
    repositoryM <- selectFirst [RepositorySlug ==. "ada/fixtures"] []
    case repositoryM of
      -- TODO: print the Repository id in the error
      Nothing -> fail "Did not find the Repository"
      Just (Entity repositoryKey _) -> do
        -- TODO: find the correct FileVersion
        fileVersionM <- selectFirst [FileVersionRepositoryId ==. repositoryKey] []
        case fileVersionM of
          -- TODO: print the FileVersion id in the error
          Nothing -> fail "Did not find the FileVersion"
          Just (Entity fileVersionKey _) -> do
            diagnosisM <- selectFirst [DiagnosisFileVersionId ==. fileVersionKey]
                                      [Desc DiagnosisNumber]
            let number = case diagnosisM of
                  Nothing -> 1
                  Just (Entity _ diagnosisValue) ->
                    1 + diagnosisNumber diagnosisValue
            foldM_ (\ currentNumber diagnosis -> do
                     saveDiagnosis fileVersionKey currentNumber diagnosis
                     return (currentNumber + 1)
                   ) number $ Result.filterDiags verbosity diagnoses

saveDiagnosis :: MonadIO m
              => FileVersionId -> Int -> Result.Diagnosis -> DBMonad m ()
saveDiagnosis fileVersionKey number diagnosis =
    let kind = case Result.diagKind diagnosis of
          Result.Error -> "Error"
          Result.Warning -> "Warning"
          Result.Hint -> "Hint"
          _ -> "Debug"
        text = Result.diagString diagnosis
        range = Result.diagPos diagnosis
    in do
         rangeKeyM <- createRange range
         insert SchemaClass.Diagnosis
           { diagnosisFileVersionId = fileVersionKey
           , diagnosisNumber = number
           , diagnosisKind = kind
           , diagnosisText = Text.pack text
           , diagnosisRangeId = rangeKeyM
           }
         return ()
