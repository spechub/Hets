{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./CASL_DL/Sublogics.hs
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

module CASL_DL.Sublogics where

import Data.Data

data CASL_DL_SL = SROIQ deriving (Eq, Ord, Typeable, Data)

instance Show CASL_DL_SL where
    show SROIQ = "SROIQ"
