module Persistence.Schema.Enums where

import Database.Persist.TH

data LocIdBaseKindType = FileVersion | NativeDocument | Library | OMS | Mapping | OpenConjecture | Theorem | CounterTheorem | Axiom | Symbol
                         deriving (Show, Read, Eq)
derivePersistField "LocIdBaseKindType"

data DiagnosisKindType = Error | Warn | Hint | Debug
                         deriving (Show, Read, Eq)
derivePersistField "DiagnosisKindType"

data ReasoningAttemptKindType = ProofAttempt | ConsistencyCheckAttempt
                                deriving (Show, Read, Eq)
derivePersistField "ReasoningAttemptKindType"
