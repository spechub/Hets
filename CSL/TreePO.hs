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

data EPCompare = Comparable Ordering | Incomparable Incomparable deriving Eq

instance Show EPCompare where
    show (Comparable LT) = "<"
    show (Comparable GT) = ">"
    show (Comparable EQ) = "="
    show (Incomparable x) = show x


-- ----------------------------------------------------------------------
-- * Combining comparison results
-- ----------------------------------------------------------------------

swapCmp :: EPCompare -> EPCompare
swapCmp (Comparable LT) = (Comparable GT)
swapCmp (Comparable GT) = (Comparable LT)
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

-}
combineCmp :: EPCompare -> EPCompare -> EPCompare
combineCmp x y
    | x == y = x -- idempotence
    | otherwise =
        case (x, y) of
          (_, Incomparable Disjoint) -> Incomparable Disjoint
          (Incomparable Overlap, _) -> Incomparable Overlap
          (Comparable EQ, _) -> y -- neutral element
          (Comparable GT, Comparable LT) -> Incomparable Overlap
          _ -> combineCmp y x -- commutative (should capture all cases)
    

