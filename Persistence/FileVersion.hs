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

module Persistence.FileVersion ( getFileVersion
                               , setFileVersionState
                               , setFileVersionStateOn
                               ) where

import Persistence.Database
import Persistence.DBConfig
import Persistence.Schema as SchemaClass
import Persistence.Schema.EvaluationStateType

import Control.Monad.IO.Class (MonadIO (..))
import Data.List (replicate)
import Database.Persist
import Database.Persist.Sql (toSqlKey, unSqlBackendKey)

setFileVersionStateOn :: MonadIO m
                      => FileVersionId -> EvaluationStateType -> DBMonad m ()
setFileVersionStateOn fileVersionKey state = do
  update fileVersionKey [FileVersionEvaluationState =. state]
  return ()

setFileVersionState :: MonadIO m
                    => DBContext -> EvaluationStateType -> DBMonad m ()
setFileVersionState dbContext state = do
  (Entity fileVersionKey _) <- getFileVersion dbContext
  setFileVersionStateOn fileVersionKey state

getFileVersion :: MonadIO m => DBContext -> DBMonad m (Entity FileVersion)
getFileVersion dbContext =
  let fileVersionS = contextFileVersion dbContext in
  if null fileVersionS
  then createNewFileVersion
  else do
        fileVersionM <-
          selectFirst [ FileVersionId ==. toSqlKey
                            (fromIntegral (read fileVersionS :: Integer))] []
        case fileVersionM of
          Nothing -> fail ("Could not find the FileVersion \"" ++
                           fileVersionS ++ "\"")
          Just fileVersion' -> return fileVersion'

createNewFileVersion :: MonadIO m => DBMonad m (Entity FileVersion)
createNewFileVersion = do
  fileVersionM <- lastFileVersion
  case fileVersionM of
    Just (Entity fileVersionKey _) ->
      let lastFileVersionId =
            fromIntegral $ unSqlBackendKey $ unFileVersionKey fileVersionKey
      in  create (lastFileVersionId + 1 :: Integer)
    Nothing -> create (1 :: Integer)
  where
    create :: (Show s, MonadIO m) => s -> DBMonad m (Entity FileVersion)
    create path = do
        Entity repositoryKey _ <- repositoryFirstOrCreate
        let fileVersionValue = FileVersion
              { fileVersionRepositoryId = repositoryKey
              , fileVersionPath = show path
              , fileVersionCommitSha = replicate 40 '0'
              , fileVersionEvaluationState = NotYetEnqueued
              }
        fileVersionKey <- insert fileVersionValue
        return $ Entity fileVersionKey fileVersionValue

lastFileVersion :: MonadIO m => DBMonad m (Maybe (Entity FileVersion))
lastFileVersion = selectFirst [] [Desc FileVersionId]

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
