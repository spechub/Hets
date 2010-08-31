{- |
Module      :  $Header$
Description :  sublogic analysis for CASL_DL
Copyright   :  (c) Dominik Luecke 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Sublogic analysis for CASL_DL

This module provides the sublogic functions (as required by Logic.hs)
  for CASL_DL. The functions allow to compute the minimal sublogics needed
  by a given element, to check whether an item is part of a given
  sublogic, and to project an element into a given sublogic.
-}

module CASL_DL.Sublogics
    (
      Lattice(..)
    , CASL_DL_SL(..)
    )
    where

import Data.Maybe()
import CASL_DL.AS_CASL_DL()
import CASL_DL.Sign()
import Logic.Logic()

class (Ord l, Show l) => Lattice l where
  cjoin :: l -> l -> l
  ctop :: l
  bot :: l

instance Lattice () where
  cjoin _ _ = ()
  ctop = ()
  bot = ()

instance Lattice Bool where
  cjoin = (||)
  ctop = True
  bot = False

data CASL_DL_SL = SROIQ
                  deriving (Ord,Eq)

instance Show CASL_DL_SL where
    show SROIQ = "SROIQ"
