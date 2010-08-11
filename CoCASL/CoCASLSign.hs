{- |
Module      :  $Header$
Description :  Signatures for CoCASL, as extension of CASL signatures
Copyright   :  (c) Till Mossakowski, Uni Bremen 2004
License     :  GPLv2 or higher
Maintainer  :  hausmann@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Signatures for CoCASL, as extension of CASL signatures.
-}

module CoCASL.CoCASLSign where

import CASL.Sign
import CASL.AS_Basic_CASL (SORT)
import qualified Data.Map as Map
import qualified Common.Lib.Rel as Rel

data CoCASLSign = CoCASLSign
  { sees :: Rel.Rel SORT
  , constructs :: Rel.Rel SORT
  , constructors :: OpMap
  } deriving (Show, Eq, Ord)

emptyCoCASLSign :: CoCASLSign
emptyCoCASLSign = CoCASLSign Rel.empty Rel.empty Map.empty

closeConsRel :: CoCASLSign -> CoCASLSign
closeConsRel s =
  s { constructs = irreflexClosure $ constructs s
    , sees = irreflexClosure $ sees s }

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
  , constructors = diffMapSet (constructors a) $ constructors b }

isSubCoCASLSign :: CoCASLSign -> CoCASLSign -> Bool
isSubCoCASLSign a b =
    Rel.isSubrelOf (sees a) (sees b)
    && Rel.isSubrelOf (constructs a) (constructs b)
    && isSubOpMap (constructors a) (constructors b)
