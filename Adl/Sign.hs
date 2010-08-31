{- |
Module      :  $Header$
Description :  ADL signature and sentences
Copyright   :  (c) Stef Joosten, Christian Maeder DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Adl.Sign where

import Adl.As
import Adl.Print ()

import Common.AS_Annotation
import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Result
import qualified Common.Lib.Rel as Rel

import qualified Data.Map as Map
import qualified Data.Set as Set

type RelMap = Map.Map Id (Set.Set RelType)

data Sign = Sign
  { rels :: RelMap
  , isas :: Rel.Rel Concept
  } deriving (Eq, Ord, Show)

emptySign :: Sign
emptySign = Sign
  { rels = Map.empty
  , isas = Rel.empty }

closeSign :: Sign -> Sign
closeSign s = s { isas = Rel.transClosure $ isas s }

isSubSignOf :: Sign -> Sign -> Bool
isSubSignOf s1 s2 =
  Map.isSubmapOfBy Set.isSubsetOf (rels s1) (rels s2)
  && Rel.isSubrelOf (isas s1) (isas s2)

signUnion :: Sign -> Sign -> Result Sign
signUnion s1 s2 = return s1
  { rels = Map.unionWith Set.union (rels s1) (rels s2)
  , isas = Rel.union (isas s1) (isas s2) }

data Symbol
  = Con Concept
  | Rel Relation
    deriving (Eq, Ord, Show)

instance GetRange Symbol where
  getRange s = case s of
    Rel r -> getRange r
    Con c -> getRange c
  rangeSpan s = case s of
    Rel r -> rangeSpan r
    Con c -> rangeSpan c

instance Pretty Symbol where
  pretty s = case s of
    Rel r -> pretty r
    Con c -> pretty c

conceptToId :: Concept -> Id
conceptToId c = case c of
  C t -> simpleIdToId t
  _ -> stringToId (show c)

symName :: Symbol -> Id
symName s = case s of
  Rel r -> simpleIdToId $ decnm r
  Con c -> conceptToId c

data RawSymbol
  = Symbol Symbol
  | AnId Id
    deriving (Eq, Ord, Show)

instance GetRange RawSymbol where
  getRange r = case r of
    Symbol s -> getRange s
    AnId i -> getRange i
  rangeSpan r = case r of
    Symbol s -> rangeSpan s
    AnId i -> rangeSpan i

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
symOf = Set.unions . map (\ (i, l) ->
          Set.fromList
            . concatMap
              (\ y -> let
                   s = relSrc y
                   t = relTrg y
                   in [Con s, Con t, Rel $ Sgn (idToSimpleId i) y])
            $ Set.toList l)
        . Map.toList . rels

instance GetRange Sign where
  getRange = getRange . symOf
  rangeSpan = rangeSpan . symOf

instance Pretty Sign where
  pretty s =
    vcat (map pretty $ concatMap (\ (i, l) ->
               map (\ t -> Pm [] (Sgn (idToSimpleId i) t) False)
               $ Set.toList l) $ Map.toList $ rels s)
    $+$ vcat (map (\ (c1, c2) -> pretty $ Pg c1 c2)
              . Rel.toList . Rel.transReduce . Rel.transClosure $ isas s)

data Sen
  = DeclProp Relation RangedProp
  | Assertion (Maybe RuleKind) Rule
    deriving (Eq, Ord, Show)

instance GetRange Sen where
  getRange s = case s of
    DeclProp _ p -> getRange p
    Assertion _ r -> getRange r
  rangeSpan s = case s of
    DeclProp r p -> joinRanges [rangeSpan r, rangeSpan p]
    Assertion _ r -> rangeSpan r

instance Pretty Sen where
  pretty s = case s of
    DeclProp r p -> pretty $ Pm [p] r False
    Assertion _ r -> pretty $ Pr Always r

printNSen :: Named Sen -> Doc
printNSen ns = let
   s = sentence ns
   n = senAttr ns
   d = pretty s
   in case s of
   Assertion (Just k) r ->
     pretty $ Pr (RuleHeader k $ mkSimpleId n) r
   _ -> d <+> text ("-- " ++ n)
