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
import qualified Persistence.Schema.Enums as Enums
import Persistence.Range
import Persistence.Schema as SchemaClass

import qualified Common.Result as Result

import Control.Monad.IO.Class (MonadIO (..))
import qualified Data.Text as Text
import Database.Persist
import Database.Persist.Sql

saveDiagnoses :: DBConfig -> DBContext -> Int -> [Result.Diagnosis] -> IO ()
saveDiagnoses dbConfig dbContext verbosity diagnoses =
  let fileVersion = contextFileVersion dbContext
  in onDatabase dbConfig $ do
      fileVersionM <-
        selectFirst [ FileVersionId ==. toSqlKey
                          (fromIntegral (read fileVersion :: Integer))] []
      case fileVersionM of
        Nothing -> fail ("Could not find the FileVersion \"" ++
                         fileVersion ++ "\"")
        Just (Entity fileVersionKey _) ->
          mapM_ (saveDiagnosis fileVersionKey) $
            Result.filterDiags verbosity diagnoses

saveDiagnosis :: MonadIO m
              => FileVersionId -> Result.Diagnosis -> DBMonad m ()
saveDiagnosis fileVersionKey diagnosis =
    let kind = case Result.diagKind diagnosis of
          Result.Error -> Enums.Error
          Result.Warning -> Enums.Warning
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
