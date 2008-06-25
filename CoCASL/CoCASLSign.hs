{- |
Module      :  $Header$
Description :  Signatures for CoCASL, as extension of CASL signatures
Copyright   :  (c) Till Mossakowski, Uni Bremen 2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
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
  } deriving (Show, Eq)

emptyCoCASLSign :: CoCASLSign
emptyCoCASLSign = CoCASLSign Rel.empty Rel.empty Map.empty

addCoCASLSign :: CoCASLSign -> CoCASLSign -> CoCASLSign
addCoCASLSign a b = a
  { sees = addRel (sees a) $ sees b
  , constructs = addRel (constructs a) $ constructs b
  , constructors = addOpMapSet (constructors a) $ constructors b }

interCoCASLSign :: CoCASLSign -> CoCASLSign -> CoCASLSign
interCoCASLSign a b = a
  { sees = interRel (sees a) $ sees b
  , constructs = interRel (constructs a) $ constructs b
  , constructors = interOpMapSet (constructors a) $ constructors b }

diffCoCASLSign :: CoCASLSign -> CoCASLSign -> CoCASLSign
diffCoCASLSign a b = a
  { sees = diffRel (sees a) $ sees b
  , constructs = diffRel (constructs a) $ constructs b
  , constructors = diffMapSet (constructors a) $ constructors b }

isSubCoCASLSign :: CoCASLSign -> CoCASLSign -> Bool
isSubCoCASLSign a b =
    Rel.isSubrelOf (sees a) (sees b)
    && Rel.isSubrelOf (constructs a) (constructs b)
    && isSubOpMap (constructors a) (constructors b)
