{- |
Module      :  $Header$
Description :
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :
Stability   :
Portability :  non-portable (imports Logic)

Data structures and functions used in Logic_THF and HasCASL2THF
-}

{-
Notes for the developer:
-- lookup monads due to the state monad
-- realworldhaskell monad

-}

module THF.Cons where

import THF.As
import THF.PrintTHF

import Common.DefaultMorphism
import Common.DocUtils
import Common.Id

-- We use the DefaultMorphism for THF.
type MorphismTHF = DefaultMorphism SignTHF

data BasicSpecTHF = BasicSpecTHF [TPTP_THF] deriving (Show, Eq, Ord)

instance GetRange BasicSpecTHF

instance Pretty BasicSpecTHF where
    pretty (BasicSpecTHF a) = printTPTPTHF a


-- Sentence

-- A Sentence is a THFFormula.
type SentenceTHF = THFFormula

instance GetRange THFFormula

instance Pretty THFFormula where
  pretty = printTHF

-- SymbolTHF

instance GetRange SymbolTHF

instance Pretty SymbolTHF where
  pretty = undefined

-- SignTHF

instance Pretty SignTHF where
  pretty = undefined

-- Creates an empty Signature.
emptySign :: SignTHF
emptySign = UNDEFINEDSIGN


