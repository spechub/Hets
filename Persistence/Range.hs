module Persistence.Range where

import Persistence.Database
import Persistence.Schema as SchemaClass

import Common.Id

import Control.Monad.IO.Class (MonadIO (..))
import Database.Persist

createRange :: MonadIO m
            => Range -> DBMonad m (Maybe FileRangeId)
createRange range =
  let rangeL = rangeToList range
  in  if null rangeL
      then return Nothing
      else
        let startPos = head rangeL
            endPosM = if null $ tail rangeL
                      then Nothing
                      else Just $ head $ tail rangeL
        in fmap Just $ insert SchemaClass.FileRange
             { fileRangePath = sourceName startPos
             , fileRangeStartLine = sourceLine startPos
             , fileRangeStartColumn = sourceColumn startPos
             , fileRangeEndLine = fmap sourceLine endPosM
             , fileRangeEndColumn = fmap sourceColumn endPosM
             }
