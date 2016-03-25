{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./CoCASL/CoCASLSign.hs
Description :  Signatures for CoCASL, as extension of CASL signatures
Copyright   :  (c) Till Mossakowski, Uni Bremen 2004
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  hausmann@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Signatures for CoCASL, as extension of CASL signatures.
-}

module CoCASL.CoCASLSign where

import CASL.Sign
import CASL.AS_Basic_CASL (SORT)

import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet

import Data.Data

data CoCASLSign = CoCASLSign
  { sees :: Rel.Rel SORT
  , constructs :: Rel.Rel SORT
  , constructors :: OpMap
  } deriving (Show, Eq, Ord, Typeable, Data)

emptyCoCASLSign :: CoCASLSign
emptyCoCASLSign = CoCASLSign Rel.empty Rel.empty MapSet.empty

closeConsRel :: CoCASLSign -> CoCASLSign
closeConsRel s =
  s { constructs = Rel.transClosure $ constructs s
    , sees = Rel.transClosure $ sees s }

addCoCASLSign :: CoCASLSign -> CoCASLSign -> CoCASLSign
addCoCASLSign a b = closeConsRel a
  { sees = Rel.union (sees a) $ sees b
  , constructs = Rel.union (constructs a) $ constructs b
  , constructors = addOpMapSet (constructors a) $ constructors b }

interCoCASLSign :: CoCASLSign -> CoCASLSign -> CoCASLSign
interCoCASLSign a b = closeConsRel a
  { sees = interRel (sees a) $ sees b
  , constructs = interRel (constructs a) $ constructs b
  , constructors = interOpMapSet (constructors a) $ constructors b }

diffCoCASLSign :: CoCASLSign -> CoCASLSign -> CoCASLSign
diffCoCASLSign a b = closeConsRel a
  { sees = Rel.difference (sees a) $ sees b
  , constructs = Rel.difference (constructs a) $ constructs b
  , constructors = diffOpMapSet (constructors a) $ constructors b }

isSubCoCASLSign :: CoCASLSign -> CoCASLSign -> Bool
isSubCoCASLSign a b =
    Rel.isSubrelOf (sees a) (sees b)
    && Rel.isSubrelOf (constructs a) (constructs b)
    && isSubOpMap (constructors a) (constructors b)
