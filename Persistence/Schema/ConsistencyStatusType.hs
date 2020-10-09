{-# LANGUAGE TemplateHaskell #-}
module Persistence.Schema.ConsistencyStatusType where

import Database.Persist.TH

-- "Contradictory" and "Open" are only used on OMS while the other two can be
-- used on ConsistencyCheckAttempt. "Contradictory" is used when there are some
-- ConsistencyCheckAttempts with "Consistent" and some with "Inconsistent".
-- "Open" is used when there are no ConsistencyCheckAttempts.
data ConsistencyStatusType = Open
                           | Timeout
                           | Error
                           | Consistent
                           | Inconsistent
                           | Contradictory
                             deriving (Show, Read, Eq)
derivePersistField "ConsistencyStatusType"
