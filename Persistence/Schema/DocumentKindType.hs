module Persistence.Schema.DocumentKindType where

import Database.Persist.TH

data DocumentKindType = Library | NativeDocument
                        deriving (Show, Read, Eq)
derivePersistField "DocumentKindType"
