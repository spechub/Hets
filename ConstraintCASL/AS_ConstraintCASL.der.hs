{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Wiebke Herding, C. Maeder, Uni Bremen 2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  portable

Abstract syntax for ConstraintCASL
  Only the formula syntax is specified
-}

module ConstraintCASL.AS_ConstraintCASL where

import Common.Id
import Common.AS_Annotation 
import CASL.AS_Basic_CASL

-- DrIFT command
{-! global: UpPos !-}

type ConstraintCASLBasicSpec = BASIC_SPEC () () ConstraintFORMULA

type ConstraintCASLFORMULA = FORMULA ConstraintFORMULA

data ConstraintFORMULA = CC
             deriving (Eq, Ord, Show)

