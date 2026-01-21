{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./Logic/SemConstr.hss
Copyright   :  (c) R. Diaconescu, IMAR, 2018
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

Semantic constraints for hybridization of institutions.

-}


module Logic.SemConstr where

import Data.Typeable
import Common.Id

-- DrIFT command:
{-! global: GetRange !-}

data SemanticConstraint = 
     ReflexiveMod | TransitiveMod | SymmetricMod | 
     SerialMod | EuclideanMod | FunctionalMod | 
     LinearMod | TotalMod | SameInterpretation String |
     SameDomain Bool  -- True for rigid partial, False for partial
     deriving (Eq, Ord, Show, Typeable)

instance GetRange SemanticConstraint where
    getRange = getRange . show
    rangeSpan = rangeSpan . show

