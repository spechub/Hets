{-# LANGUAGE TemplateHaskell #-}
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

-- "CONTR" is only used on Conjecture while the others can be used on
-- ProofAttempt. "CONTR" is used when there are some ProofAttempts with "THM"
-- and some with "CSA".
data ProofStatusType = OPN | ERR | UNK | RSO | THM | CSA | CSAS | CONTR
                       deriving (Show, Read, Eq)
derivePersistField "ProofStatusType"

data ReasonerKindType = Prover | ConsistencyChecker
                         deriving (Show, Read, Eq)
derivePersistField "ReasonerKindType"

data PremiseSelectionKindType = ManualPremiseSelection | SinePremiseSelection
                                deriving (Show, Read, Eq)
derivePersistField "PremiseSelectionKindType"
