module Persistence.Schema.ReasoningStatusOnConjectureType where

import Database.Persist.TH

data ReasoningStatusOnConjectureType = OPN | ERR | UNK | RSO | THM | CSA
                                       | CSAS | CONTR
                                       deriving (Show, Read, Eq)
derivePersistField "ReasoningStatusOnConjectureType"
