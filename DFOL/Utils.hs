{- |
Module      :  $Header$
Description :  Utilities for first-order logic with dependent types (DFOL)
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2009
License     :  GPLv2 or higher

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module DFOL.Utils where

import qualified Common.Result as Result

-- logical operators precedences
truePrec :: Int
truePrec = 1

falsePrec :: Int
falsePrec = 1

predPrec :: Int
predPrec = 1

equalPrec :: Int
equalPrec = 1

negPrec :: Int
negPrec = 2

conjPrec :: Int
conjPrec = 3

disjPrec :: Int
disjPrec = 3

implPrec :: Int
implPrec = 4

equivPrec :: Int
equivPrec = 4

forallPrec :: Int
forallPrec = 5

existsPrec :: Int
existsPrec = 5

sortPrec :: Int
sortPrec = 1

formPrec :: Int
formPrec = 1

univPrec :: Int
univPrec = 1

funcPrec :: Int
funcPrec = 2

piPrec :: Int
piPrec = 3

-- datatype for items annotated with diagnostic messages
data DIAGN a = Diagn
    { diags :: [Result.Diagnosis]
    , item  :: a
    } deriving (Show, Eq)

-- conjunction for a list of truth values with diagnostic messages
andD :: [DIAGN Bool] -> DIAGN Bool
andD xs = Diagn diag result
          where result = and $ map item xs
                diag = concat $ map diags xs
