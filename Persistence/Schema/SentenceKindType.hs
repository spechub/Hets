module Persistence.Schema.SentenceKindType where

import Database.Persist.TH

data SentenceKindType = OpenConjecture | Theorem | CounterTheorem | Axiom
                        deriving (Show, Read, Eq)
derivePersistField "SentenceKindType"
