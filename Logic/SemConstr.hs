{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./Logic/SemConstr.hs
Description :  abstract syntax of DOL documents and CASL specification libraries
Copyright   :  (c) Klaus Luettich, Uni Bremen 2002-2016
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

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

