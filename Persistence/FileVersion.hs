{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}

{- |
Module      :  Persistence.Diagnosis.hs
Copyright   :  (c) Uni Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  portable
-}

module Persistence.FileVersion ( getFileVersion
                               , setFileVersionState
                               , setFileVersionStateOn
                               ) where

import Persistence.Database
import Persistence.DBConfig
import Persistence.Schema as SchemaClass
import Persistence.Schema.EvaluationStateType

import Control.Monad.IO.Class (MonadIO (..))
import qualified Control.Monad.Fail as Fail
import Database.Persist
import Database.Persist.Sql (toSqlKey)

setFileVersionStateOn :: (MonadIO m, Fail.MonadFail m)
                      => FileVersionId -> EvaluationStateType -> DBMonad m ()
setFileVersionStateOn fileVersionKey state = do
  Just fileVersionValue <- get fileVersionKey
  update (fileVersionActionId fileVersionValue) [ActionEvaluationState =. state]
  return ()

setFileVersionState :: (MonadIO m, Fail.MonadFail m)
                    => DBContext -> EvaluationStateType -> DBMonad m ()
setFileVersionState dbContext state = do
  (Entity fileVersionKey _) <- getFileVersion dbContext
  setFileVersionStateOn fileVersionKey state

getFileVersion :: (MonadIO m, Fail.MonadFail m) => DBContext -> DBMonad m (Entity FileVersion)
getFileVersion dbContext =
  let fileVersionS = contextFileVersion dbContext in
  if null fileVersionS
  then  findOrCreateFileVersion dbContext -- Hets has not been called by Ontohub
  else do -- Hets has been called by Ontohub
        fileVersionM <-
          selectFirst [ FileVersionId ==. toSqlKey
                            (fromIntegral (read fileVersionS :: Integer))] []
        case fileVersionM of
          Nothing -> Fail.fail ("Could not find the FileVersion \"" ++
                           fileVersionS ++ "\"")
          Just fileVersion' -> return fileVersion'

nonGitFileVersion :: String
nonGitFileVersion = "non-git FileVersion"

findOrCreateFileVersion :: forall m . MonadIO m
                        => DBContext -> DBMonad m (Entity FileVersion)
findOrCreateFileVersion dbContext = do
  let path = contextFilePath dbContext
  fileVersionM <- lastFileVersion path
  case fileVersionM of
    Just fileVersion -> return fileVersion
    Nothing -> create path
  where
    create :: MonadIO m => FilePath -> DBMonad m (Entity FileVersion)
    create path = do
        Entity repositoryKey _ <- repositoryFirstOrCreate
        actionKey <- insert Action
          { actionEvaluationState = NotYetEnqueued
          , actionMessage = Nothing
          }
        let fileVersionValue = FileVersion
              { fileVersionActionId = actionKey
              , fileVersionRepositoryId = repositoryKey
              , fileVersionPath = path
              , fileVersionCommitSha = nonGitFileVersion
              }
        fileVersionKey <- insert fileVersionValue
        return $ Entity fileVersionKey fileVersionValue

lastFileVersion :: MonadIO m
                => FilePath -> DBMonad m (Maybe (Entity FileVersion))
lastFileVersion path =
  selectFirst [ FileVersionPath ==. path
              , FileVersionCommitSha ==. nonGitFileVersion
              ] [Desc FileVersionId]

repositoryFirstOrCreate :: MonadIO m => DBMonad m (Entity Repository)
repositoryFirstOrCreate = do
  repositoryM <- selectFirst [] []
  case repositoryM of
    Just repository -> return repository
    Nothing -> do
      Entity ownerKey _ <- organizationalUnitFirstOrCreate
      let repositoryValue = Repository { repositoryOwnerId = ownerKey }
      repositoryKey <- insert repositoryValue
      return $ Entity repositoryKey repositoryValue

organizationalUnitFirstOrCreate :: MonadIO m
                                => DBMonad m (Entity OrganizationalUnit)
organizationalUnitFirstOrCreate = do
  organizationalUnitM <- selectFirst [] []
  case organizationalUnitM of
    Just organizationalUnit -> return organizationalUnit
    Nothing -> do
      let organizationalUnitValue = OrganizationalUnit
            { organizationalUnitKind = "Organization"
            , organizationalUnitSlug = "dummy"
            }
      organizationalUnitKey <- insert organizationalUnitValue
      return $ Entity organizationalUnitKey organizationalUnitValue
