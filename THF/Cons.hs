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

module THF.Cons where

import THF.As
import THF.PrintTHF

import Common.DefaultMorphism
import Common.DocUtils
import Common.Id

-- We use the DefaultMorphism for THF.
type THFMorphism = DefaultMorphism Sign

-- Sentence

-- A Sentence is a THFFormula.
type Sentence = THFFormula

instance GetRange THFFormula

instance Pretty THFFormula where
  pretty = printTHF


-- Sign

instance Pretty Sign where
  pretty = undefined

-- Creates an empty Signature.
emptySign :: Sign
emptySign = UNDEFINEDSIGN


-- Symbol

instance GetRange Symbol

instance Pretty Symbol where
  pretty = undefined
