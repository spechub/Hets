{- |
Module      :  $Header$
Description :  ADL signature and sentences
Copyright   :  (c) Stef Joosten, Christian Maeder DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Adl.Sign where

import Adl.As
import Adl.Print ()

import qualified Common.Lib.Rel as Rel
import Common.DocUtils
import Common.Id
import Common.Result

import qualified Data.Map as Map
import qualified Data.Set as Set

data RelType = RelType
  { relSrc :: Concept
  , relTrg :: Concept
  } deriving (Eq, Ord, Show)

type RelMap = Map.Map Id (Set.Set RelType)

data Sign = Sign
  { rels :: RelMap
  , isas :: Rel.Rel Concept
  } deriving (Eq, Ord, Show)

emptySign :: Sign
emptySign = Sign
  { rels = Map.empty
  , isas = Rel.empty }

isSubSignOf :: Sign -> Sign -> Bool
isSubSignOf s1 s2 =
  Map.isSubmapOfBy Set.isSubsetOf (rels s1) (rels s2)
  && Rel.isSubrelOf (isas s1) (isas s2)

signUnion :: Sign -> Sign -> Result Sign
signUnion s1 s2 = return s1
  { rels = Map.unionWith Set.union (rels s1) (rels s2)
  , isas = Rel.union (isas s1) (isas s2) }

symOf :: Sign -> Set.Set Relation
symOf = Set.unions . map (\ (i, s) ->
          Set.map (\ t -> Sgn (show i) (relSrc t) $ relTrg t) s)
        . Map.toList . rels

instance Pretty Sign where
  pretty = pretty . symOf

instance GetRange Sign

data Sen
  = DeclProp Relation Prop
  | Assertion Rule
    deriving (Eq, Ord, Show)

instance GetRange Sen

instance Pretty Sen where
  pretty s = case s of
    DeclProp r p -> pretty $ Pm [p] r
    Assertion r -> pretty r
