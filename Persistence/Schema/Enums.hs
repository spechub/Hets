module Persistence.Schema.Enums where

import Database.Persist.TH

data LocIdBaseKindType = FileVersion | NativeDocument | Library | OMS | Mapping | OpenConjecture | Theorem | CounterTheorem | Axiom | Symbol
                         deriving (Show, Read, Eq)
derivePersistField "LocIdBaseKindType"

data ErrorKindType = SyntaxError
                     deriving (Show, Read, Eq)
derivePersistField "ErrorKindType"

data ReasoningAttemptKindType = ProofAttempt | ConsistencyCheckAttempt
                                deriving (Show, Read, Eq)
derivePersistField "ReasoningAttemptKindType"
