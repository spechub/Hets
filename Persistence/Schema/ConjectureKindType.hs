module Persistence.Schema.ConjectureKindType where

import Database.Persist.TH

data ConjectureKindType = OpenConjecture | Theorem | CounterTheorem
                          deriving (Show, Read, Eq)
derivePersistField "ConjectureKindType"
