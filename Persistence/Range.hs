module Persistence.Range where

import Persistence.Database
import Persistence.Schema as SchemaClass hiding (Range)
import qualified Persistence.Schema as SchemaClass (Range (..))

import Common.Id

import Control.Monad.IO.Class (MonadIO (..))
import Database.Persist

createRange :: MonadIO m
            => Range -> DBMonad m (Maybe RangeId)
createRange range =
  let rangeL = rangeToList range
  in  if null rangeL
      then return Nothing
      else
        let startPos = head rangeL
            endPosM = if null $ tail rangeL
                      then Nothing
                      else Just $ head $ tail rangeL
        in fmap Just $ insert SchemaClass.Range
             { rangePath = sourceName startPos
             , rangeStartLine = sourceLine startPos
             , rangeStartColumn = sourceColumn startPos
             , rangeEndLine = fmap sourceLine endPosM
             , rangeEndColumn = fmap sourceColumn endPosM
             }
