{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Handling of tree-like partial ordering relations
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  portable

This module defines a basic datatype for tree-like partial orderings such as
encountered, e.g., in the set lattice.
 -}

module CSL.TreePO
{-    ( Incomparable (..)
    , SetOrdering (..)
    , SetOrInterval (..)
    , swapCompare
    , swapCmp
    , combineCmp
    ) -}
    where

import qualified Data.Set as Set

-- ----------------------------------------------------------------------
-- * Datatypes for comparison
-- ----------------------------------------------------------------------

data Incomparable = Disjoint | Overlap deriving (Eq, Show)

data SetOrdering = Comparable Ordering | Incomparable Incomparable deriving Eq

instance Show SetOrdering where
    show (Comparable LT) = "<"
    show (Comparable GT) = ">"
    show (Comparable EQ) = "="
    show (Incomparable x) = show x


data InfDev = EpsLeft | Zero | EpsRight deriving (Eq, Show)

instance Ord InfDev where
    compare EpsLeft Zero = LT
    compare EpsLeft EpsRight = LT
    compare Zero EpsRight = LT
    compare x y 
        | x == y = EQ
        | otherwise = swapCompare $ compare y x

-- | This type with the given ordering is to represent opened/closed intervals
--   over 'a' as closed intervals over '(a, InfDev)'
instance Ord a => Ord (a, InfDev) where
    compare (x, a) (y, b) =
        case compare x y of
          EQ -> compare a b
          res -> res


-- | A left right indicator datatype
data Direction = DLeft | DRight

-- | Configurations for two closed intervals
data OrdInt = OIDisj               -- are disjoint
            | OITouch1             -- first right border touches second left border
            | OITouch2             -- first left border touches second right border
            | OIEq                 -- both are equal
            -- first contains second and evtl. touches at the direction point
            | OIContain1 (Maybe Direction)
            -- second contains first and evtl. touches at the direction point
            | OIContain2 (Maybe Direction)
            | OIOverlap            -- both really overlap


-- | A finite set or an interval. True = closed, False = opened interval border.
data SetOrInterval a = Set (Set.Set a)
                     | IntVal (a, Bool) (a, Bool)
                       deriving (Eq, Ord, Show)


-- | Compares closed intervals [l1, r1] and [l2, r2]. Assumes
-- | non-singular intervals, i.e., l1 < r1 and l2 < r2.
-- | Works only for linearly ordered types.
cmpClosedInts :: Ord a => a -- ^ l1
              -> a -- ^ r1
              -> a -- ^ l2
              -> a -- ^ r2
              -> OrdInt
cmpClosedInts l1 r1 l2 r2
    | l1 == l2 && r1 == r2 = OIEq
    | r1 == l2 = OITouch1
    | r2 == l1 = OITouch2
    | l1 <= l2 && r1 >= r2 = mkContain OIContain1
    | l1 >= l2 && r1 <= r2 = mkContain OIContain2
    | r1 < l2 || r2 < l1 = OIDisj
    | otherwise = OIOverlap
    where mkContain f
              | l1 == l2 = f $ Just DLeft
              | r1 == r2 = f $ Just DRight
              | otherwise = f $ Nothing


-- ----------------------------------------------------------------------
-- * Combining comparison results
-- ----------------------------------------------------------------------

membSoI :: Ord a => a -> SetOrInterval a -> Bool
membSoI gc (Set s) = Set.member gc s
membSoI gc (IntVal (a, bA) (b, bB)) =
    let opA = if bA then (>=) else (>)
        opB = if bB then (<=) else (<)
    in opA gc a && opB gc b

nullSoI :: Ord a => SetOrInterval a -> Bool
nullSoI (Set s) = Set.null s
nullSoI (IntVal (a, bA) (b, bB)) = a == b && not (bA && bB)

-- | If the set is singular, i.e., consists only from one point, then we
-- return this point. Reports error on empty SoI's.
toSingular :: Ord a => SetOrInterval a -> Maybe a
toSingular d
    | nullSoI d = error "toSingular: empty set"
    | otherwise =
        case d of
          Set s
              | Set.size s == 1 -> Just $ Set.findMin s
              | otherwise -> Nothing
          IntVal (a, _) (b, _)
              | a == b -> Just a
              | otherwise -> Nothing


cmpSoIs :: Ord a => SetOrInterval a -> SetOrInterval a -> SetOrdering
cmpSoIs d1 d2 =
    case (toSingular d1, toSingular d2) of
      (Just gc1, Just gc2)
          | gc1 == gc2 -> Comparable EQ
          | otherwise -> Incomparable Disjoint
      (Just gc, _)
          | membSoI gc d2 -> Comparable LT
          | otherwise -> Incomparable Disjoint
      (_, Just gc)
          | membSoI gc d1 -> Comparable GT
          | otherwise -> Incomparable Disjoint
      _ -> cmpSoIsEx d1 d2 -- singular cases are dispelled here


cmpSoIsEx :: Ord a => SetOrInterval a -> SetOrInterval a -> SetOrdering
cmpSoIsEx (Set s1) (Set s2)
    | s1 == s2 = Comparable EQ
    | s1 `Set.isSubsetOf` s2 = Comparable LT
    | s2 `Set.isSubsetOf` s1 = Comparable GT
    | Set.null $ Set.intersection s1 s2 = Incomparable Disjoint
    | otherwise = Incomparable Overlap

cmpSoIsEx (IntVal (l1, bL1) (r1, bR1)) (IntVal (l2, bL2) (r2, bR2)) =
    case cmpClosedInts l1 r1 l2 r2 of
      OIDisj -> Incomparable Disjoint
      OITouch1 -> touchRes bR1 bL2
      OITouch2 -> touchRes bR2 bL1
      OIEq -- assumes that True > False:
          | bL1 == bL2 && bR1 == bR2 -> Comparable EQ
          | bL1 >= bL2 && bR1 >= bR2 -> Comparable GT
          | bL1 <= bL2 && bR1 <= bR2 -> Comparable LT
          | otherwise -> Incomparable Overlap
      OIContain1 mDir ->
          case mDir of
            Just DLeft -> containRes bL1 bL2
            Just DRight -> containRes bR1 bR2
            Nothing -> Comparable GT
      OIContain2 mDir ->
          case mDir of
            Just DLeft -> swapCmp $ containRes bL2 bL1
            Just DRight -> swapCmp $ containRes bR2 bR1
            Nothing -> Comparable GT
      OIOverlap -> Incomparable Overlap
    where touchRes b1 b2 = if b1 && b2 then Incomparable Overlap
                           else Incomparable Disjoint
          containRes b1 b2 = if b1 >= b2 then Comparable GT
                             else Incomparable Overlap

{-
cmpSoIsEx (IntVal (a,bA) (b, bB)) (Set s1) = error ""
    case cmpClosedInts a b l2 r2 of

cmpSoIsEx d1@(Set s1) i = swapCmp $ cmpSoIsEx i d1
-}
cmpSoIsEx _ _ = error "cmpSoIsEx"



-- ----------------------------------------------------------------------
-- * Combining comparison results
-- ----------------------------------------------------------------------

swapCompare :: Ordering -> Ordering
swapCompare GT = LT
swapCompare LT = GT
swapCompare x = x


swapCmp :: SetOrdering -> SetOrdering
swapCmp (Comparable x) = Comparable $ swapCompare x
swapCmp x = x

{- | We combine the comparison outcome of the individual parameters with
     the following (symmetrical => commutative) table:

>     \ | > < = O D
>     -------------
>     > | > O > O D
>     < |   < < O D
>     = |     = O D
>     O |       O D
>     D |         D
>
>     , where
>
>     >       | <      | =     | O       | D
>     ---------------------------------------------
>     RightOf | LeftOf | Equal | Overlap | Disjoint


The purpose of this table is to use it for cartesian products as follows

Let

A', A'' \subset A
B', B'' \subset B


In order to get the comparison result for A' x B' and A'' x B'' we compare

A' and A'' as well as B' and B'' and combine the results with the above table.

Note that for empty sets the comparable results <,>,= are preferred over the
disjoint result.
-}

combineCmp :: SetOrdering -> SetOrdering -> SetOrdering
combineCmp x y
    | x == y = x -- idempotence
    | otherwise =
        case (x, y) of
          (_, Incomparable Disjoint) -> Incomparable Disjoint
          (Incomparable Overlap, _) -> Incomparable Overlap
          (Comparable EQ, _) -> y -- neutral element
          (Comparable GT, Comparable LT) -> Incomparable Overlap
          _ -> combineCmp y x -- commutative (should capture all cases)
    

