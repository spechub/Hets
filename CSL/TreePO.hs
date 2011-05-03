{- |
Module      :  $Header$
Description :  Handling of tree-like partial ordering relations
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  portable

This module defines a basic datatype for tree-like partial orderings.
 -}

module CSL.TreePO where

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
    

