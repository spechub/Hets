{- |
Module      :  $Header$
Description :  signatures for FPL
Copyright   :  (c) Christian Maeder, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

signature extension for FPL to keep track of constructors

This signature type is complete unused currently and likely to change.
Constructors could also be kept directly via CASL as extra OpMap and thus
making this extension obsolete.
-}

module Fpl.Sign where

import Common.Doc
import Common.DocUtils
import Common.Id

import CASL.Sign

import qualified Data.Map as Map
import qualified Data.Set as Set

data SignExt = SignExt
  { constr :: Map.Map Id OpType
  , freetypes :: Map.Map Id (Set.Set (Id, OpType)) }
  deriving (Show, Eq, Ord)

instance Pretty SignExt where
  pretty _ = empty

emptyFplSign :: SignExt
emptyFplSign = SignExt Map.empty Map.empty

addFplSign :: SignExt -> SignExt -> SignExt
addFplSign s1 s2 = s1
  { constr = Map.union (constr s1) $ constr s2
  , freetypes = Map.unionWith Set.union (freetypes s1) $ freetypes s2 }

isSubFplSign :: SignExt -> SignExt -> Bool
isSubFplSign s1 s2 =
  Map.isSubmapOf (constr s1) (constr s2) &&
  Map.isSubmapOf (freetypes s1) (freetypes s2)
