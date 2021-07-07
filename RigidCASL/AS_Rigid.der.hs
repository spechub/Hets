{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./RigidCASL/AS_Rigid.der.hs
Copyright   :  (c) M. Codescu, IMAR, 2018
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.com
Stability   :  provisional
Portability :  portable

Abstract syntax for rigid extension of CASL
-}

module RigidCASL.AS_Rigid where

import Common.Id
import Common.AS_Annotation

import CASL.AS_Basic_CASL
import CASL.Sign

import Data.Data

-- DrIFT command
{-! global: GetRange !-}

type R_BASIC_SPEC = BASIC_SPEC () R_SIG_ITEM ()

data R_SIG_ITEM =
          Rigid_sorts [Annoted (SORT_ITEM ())] Range
        | Rigid_op_items [Annoted (OP_ITEM ())] Range
        | Rigid_pred_items [Annoted (PRED_ITEM ())] Range
             deriving (Show, Typeable, Data)

data RigidSymbol = CSym Symbol | RSym Symbol
  deriving (Show, Eq, Ord, Typeable, Data)
