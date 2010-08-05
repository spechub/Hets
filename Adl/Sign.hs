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

data Symbol
  = Rel Relation
  | Con Concept
    deriving (Eq, Ord, Show)

instance GetRange Symbol
instance Pretty Symbol where
  pretty s = case s of
    Rel r -> pretty r
    Con c -> pretty c

symName :: Symbol -> Id
symName s = simpleIdToId $ case s of
  Rel r -> decnm r
  Con (C c) -> c
  Con c -> mkSimpleId $ show c

data RawSymbol
  = Symbol Symbol
  | AnId Id
    deriving (Eq, Ord, Show)

instance GetRange RawSymbol
instance Pretty RawSymbol where
  pretty r = case r of
    Symbol s -> pretty s
    AnId i -> pretty i

symMatch :: Symbol -> RawSymbol -> Bool
symMatch s r = case r of
  Symbol t -> s == t
  AnId i -> symName s == i

idToSimpleId :: Id -> Token
idToSimpleId i = case i of
  Id [t] [] _ -> t
  _ -> error $ "idToSimpleId: " ++ show i

symOf :: Sign -> Set.Set Symbol
symOf = Set.unions . map (\ (i, s) ->
          Set.map (\ t -> Rel $ Sgn (idToSimpleId i) (relSrc t) $ relTrg t) s)
        . Map.toList . rels

instance GetRange Sign
instance Pretty Sign where
  pretty = pretty . symOf

data Sen
  = DeclProp Relation RangedProp
  | Assertion (Maybe RuleKind) Rule
    deriving (Eq, Ord, Show)

instance GetRange Sen
instance Pretty Sen where
  pretty s = case s of
    DeclProp r p -> pretty $ Pm [p] r False
    Assertion _ r -> pretty $ Pr Always r
