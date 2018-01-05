module Persistence.Schema.ReasoningStatusOnReasoningAttemptType where

import Database.Persist.TH

data ReasoningStatusOnReasoningAttemptType = OPN | ERR | UNK | RSO | THM | CSA
                                           | CSAS
                                             deriving (Show, Read, Eq)
derivePersistField "ReasoningStatusOnReasoningAttemptType"
