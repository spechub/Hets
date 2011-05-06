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


{- | We represent Intervals with opened or closed end points over a linearly
   ordered type 'a' as closed intervals over the type '(a, InfDev)', for
   infinitesimal deviation.
   - '(x, EpsLeft)' means an epsilon to the left of x
   - '(x, Zero)' means x
   - '(x, EpsRight)' means an epsilon to the right of x
   We have EpsLeft < Zero < EpsRight and the ordering of 'a' lifts to the
   lexicographical ordering of '(a, InfDev)' which captures well our intended
   meaning.
   We inject the type 'a' into the type '(a, InfDev)'
   by mapping 'x' to '(x, Zero)'.
   The mapping of intrvals is as follows:
   A left opened interval starting at x becomes a left closed interval starting
   at '(x, EpsRight)'.
   We have:
   'forall y > x. (y, _) > (x, EpsRight)', hence in particular
   '(y, Zero) > (x, EpsRight)'
   but also
   '(x, Zero) < (x, EpsRight)'

   Analogously we represent a right opened one ending at y as a closed one
   ending at '(x, EpsLeft)'.
-}
data InfDev = EpsLeft | Zero | EpsRight deriving (Eq, Show)

instance Ord InfDev where
    compare x y 
        | x == y = EQ
        | otherwise =
            case (x, y) of
              (EpsLeft, _) -> LT
              (EpsRight, _) -> GT
              _ -> swapCompare $ compare y x

newtype CIType a = CIType (a, InfDev) deriving (Eq, Show)

-- | This type with the given ordering is to represent opened/closed intervals
--   over 'a' as closed intervals over '(a, InfDev)'
instance Ord a => Ord (CIType a) where
    compare (CIType (x, a)) (CIType (y, b)) =
        case compare x y of
          EQ -> compare a b
          res -> res


-- | A finite set or an interval. True = closed, False = opened interval border.
data SetOrInterval a = Set (Set.Set a)
                     | IntVal (a, Bool) (a, Bool)
                       deriving (Eq, Ord, Show)

-- | Infinite integers = integers augmented by -Infty and +Infty
data InfInt = PosInf | NegInf | FinInt Integer deriving (Show, Eq)

instance Ord InfInt where
    compare x y
        | x == y = EQ
        | otherwise =
            case (x, y) of
              (NegInf, _) -> LT
              (PosInf, _) -> GT
              (FinInt a, FinInt b) -> compare a b
              _ -> swapCompare $ compare y x


class Continuous a

class Discrete a where
    nextA :: a -> a
    prevA :: a -> a
    intsizeA :: a -> a -> Maybe Integer


instance Discrete InfInt where
    nextA (FinInt a) = FinInt $ a+1
    nextA x = x
    prevA (FinInt a) = FinInt $ a-1
    prevA x = x
    intsizeA (FinInt a) (FinInt b) = Just $ (1+) $ abs $ b-a
    intsizeA _ _ = Nothing

-- ----------------------------------------------------------------------
-- * Comparison facility for sets
-- ----------------------------------------------------------------------

-- | Compares closed intervals [l1, r1] and [l2, r2]. Assumes
-- | non-singular intervals, i.e., l1 < r1 and l2 < r2.
-- | Works only for linearly ordered types.
cmpClosedInts :: Ord a => (a, a) -- ^ [l1, r1]
              -> (a, a) -- ^ [l2, r2]
              -> SetOrdering
cmpClosedInts (l1, r1) (l2, r2)
    | l1 == l2 && r1 == r2 = Comparable EQ
    | l1 <= l2 && r1 >= r2 = Comparable GT
    | l1 >= l2 && r1 <= r2 = Comparable LT
    | r1 < l2 || r2 < l1 = Incomparable Disjoint
    | otherwise = Incomparable Overlap

-- ----------------------------------------------------------------------
-- ** Comparison for discrete types
-- ----------------------------------------------------------------------

-- | Membership in 'SetOrInterval'
membSoID :: (Discrete a, Ord a) => a -> SetOrInterval a -> Bool
membSoID x (Set s) = Set.member x s
membSoID x i = let (a, b) = setToClosedIntD i in x >= a && x <= b

-- | Checks if the set is empty.
nullSoID :: (Discrete a, Ord a) => SetOrInterval a -> Bool
nullSoID (Set s) = Set.null s
nullSoID i = let (a, b) = setToClosedIntD i in a > b

-- | If the set is singular, i.e., consists only from one point, then we
-- return this point. Reports error on empty SoI's.
toSingularD :: (Discrete a, Ord a) => SetOrInterval a -> Maybe a
toSingularD d
    | nullSoID d = error "toSingularD: empty set"
    | otherwise =
        case d of
          Set s
              | Set.size s == 1 -> Just $ Set.findMin s
              | otherwise -> Nothing
          _ -> let (a, b) = setToClosedIntD d
               in if a == b then Just a else Nothing

-- | Transforms a 'SetOrInterval' to a closed representation
setToClosedIntD :: (Discrete a, Ord a) =>  SetOrInterval a -> (a, a)
setToClosedIntD (Set s) = (Set.findMin s, Set.findMax s)
setToClosedIntD (IntVal (l, bL) (r, bR)) =
    (if bL then l else nextA l, if bR then r else prevA r)


-- | Compare sets over discrete types
cmpSoIsD :: (Discrete a, Ord a) =>
           SetOrInterval a -> SetOrInterval a -> SetOrdering
cmpSoIsD d1 d2 =
    case (toSingularD d1, toSingularD d2) of
      (Just x1, Just x2)
          | x1 == x2 -> Comparable EQ
          | otherwise -> Incomparable Disjoint
      (Just x, _)
          | membSoID x d2 -> Comparable LT
          | otherwise -> Incomparable Disjoint
      (_, Just x)
          | membSoID x d1 -> Comparable GT
          | otherwise -> Incomparable Disjoint
      _ -> cmpSoIsExD d1 d2 -- singular cases are dispelled here


-- | Compare sets helper function which only works on regular (non-singular)
-- sets
cmpSoIsExD :: (Discrete a, Ord a) =>
              SetOrInterval a -> SetOrInterval a -> SetOrdering
cmpSoIsExD i1@(IntVal _ _) i2@(IntVal _ _) =
    cmpClosedInts (setToClosedIntD i1) $ setToClosedIntD i2

cmpSoIsExD s1@(Set _) s2@(Set _) = cmpSoIsEx s1 s2

cmpSoIsExD i1@(IntVal _ _) s2@(Set s) =
    let ci2@(a2, b2) = setToClosedIntD s2
    in case cmpClosedInts (setToClosedIntD i1) ci2 of
      Comparable EQ -> case intsizeA a2 b2 of
                         Just dst 
                             | fromIntegral (Set.size s) == dst ->
                                 Comparable EQ
                             | otherwise -> Comparable GT
                         -- Nothing means infinite. This is a misuse!
                         _ -> error "cmpSoIsExD: unbounded finite set!"
      Comparable LT -> if any (flip membSoID i1) $ Set.toList s
                       then Incomparable Overlap
                       else Incomparable Disjoint
      so -> so

cmpSoIsExD s1 i2 = swapCmp $ cmpSoIsExD i2 s1

-- ----------------------------------------------------------------------
-- ** Comparison for continuous types
-- ----------------------------------------------------------------------

-- | Membership in 'SetOrInterval'
membSoI :: Ord a => a -> SetOrInterval a -> Bool
membSoI x (Set s) = Set.member x s
membSoI x i = let (a, b) = setToClosedInt i
                  x' = CIType (x, Zero) in x' >= a && x' <= b

-- | Checks if the set is empty.
-- Only for continuous types.
nullSoI :: (Continuous a, Ord a) => SetOrInterval a -> Bool
nullSoI (Set s) = Set.null s
nullSoI (IntVal (a, bA) (b, bB)) = a == b && not (bA && bB)

-- | If the set is singular, i.e., consists only from one point, then we
-- return this point. Reports error on empty SoI's.
-- Only for continuous types.
toSingular :: (Continuous a, Ord a) => SetOrInterval a -> Maybe a
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

-- | Transforms a 'SetOrInterval' to a closed representation
-- Only for continuous types.
setToClosedInt :: Ord a => 
                  SetOrInterval a -> (CIType a, CIType a)
setToClosedInt (Set s) = ( CIType (Set.findMin s, Zero)
                         , CIType (Set.findMax s, Zero))
setToClosedInt (IntVal (l, bL) (r, bR)) =
    ( CIType (l, if bL then Zero else EpsRight)
    , CIType (r, if bR then Zero else EpsLeft))

-- | Compare sets over continuous types
cmpSoIs :: (Continuous a, Ord a) =>
           SetOrInterval a -> SetOrInterval a -> SetOrdering
cmpSoIs d1 d2 =
    case (toSingular d1, toSingular d2) of
      (Just x1, Just x2)
          | x1 == x2 -> Comparable EQ
          | otherwise -> Incomparable Disjoint
      (Just x, _)
          | membSoI x d2 -> Comparable LT
          | otherwise -> Incomparable Disjoint
      (_, Just x)
          | membSoI x d1 -> Comparable GT
          | otherwise -> Incomparable Disjoint
      _ -> cmpSoIsEx d1 d2 -- singular cases are dispelled here



-- | Compare sets helper function which only works on regular (non-singular)
-- sets
cmpSoIsEx :: (Ord a) => SetOrInterval a -> SetOrInterval a -> SetOrdering
cmpSoIsEx (Set s1) (Set s2)
    | s1 == s2 = Comparable EQ
    | s1 `Set.isSubsetOf` s2 = Comparable LT
    | s2 `Set.isSubsetOf` s1 = Comparable GT
    | Set.null $ Set.intersection s1 s2 = Incomparable Disjoint
    | otherwise = Incomparable Overlap

cmpSoIsEx i1@(IntVal _ _) i2@(IntVal _ _) =
    cmpClosedInts (setToClosedInt i1) $ setToClosedInt i2

cmpSoIsEx i1@(IntVal _ _) s2@(Set s) =
    case cmpClosedInts (setToClosedInt i1) $ setToClosedInt s2 of
      Comparable EQ -> Comparable GT
      Comparable LT -> if any (flip membSoI i1) $ Set.toList s
                       then Incomparable Overlap
                       else Incomparable Disjoint
      so -> so

cmpSoIsEx s1 i2 = swapCmp $ cmpSoIsEx i2 s1


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
    

