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

module Persistence.FileVersion where

import Persistence.Database
import Persistence.DBConfig
import qualified Persistence.Schema.EvaluationStateType as EvaluationStateType
import Persistence.Schema as SchemaClass

import Control.Monad.IO.Class (MonadIO (..))
import Database.Persist
import Database.Persist.Sql (toSqlKey)

setFileVersionState :: MonadIO m
                    => DBContext -> EvaluationStateType.EvaluationStateType
                    -> DBMonad m ()
setFileVersionState dbContext state = do
  (Entity fileVersionKey _) <- getFileVersion dbContext
  update fileVersionKey [FileVersionEvaluationState =. state]
  return ()

getFileVersion :: MonadIO m => DBContext -> DBMonad m (Entity FileVersion)
getFileVersion dbContext =
  let fileVersionS = contextFileVersion dbContext in do
    fileVersionM <-
      selectFirst [ FileVersionId ==. toSqlKey
                        (fromIntegral (read fileVersionS :: Integer))] []
    case fileVersionM of
      Nothing -> fail ("Could not find the FileVersion \"" ++
                       fileVersionS ++ "\"")
      Just fileVersion' -> return fileVersion'
