{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
{- |
Module      :  $Header$
Description :  Handling of extended parameters
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  non-portable

This module defines an ordering on extended parameters and other analysis tools.

Extended parameters may be based on one of the following
     relations:

>    =, <=, >=, !=, <, >, -|

     We reduce the relations to one of the Data items in 'NormEP'.  We
     handle @-|@ as @*@ for comparison and range computations, i.e.,
     we remove it, and @< n@ is turned into @<= n-1@
     (or @'LeftOf' n-1@) and accordingly for @>@.

     We could work more generally with a sequence of intervals which
     generalizes sets representable by the given relations and with
     the advantage that this representation is closed under union,
     intersection and complement. Such sequences could be represented
     by an ordered sequence of their borders, e.g.

>    <=1,=3, as [-oo,2,2,4,oo]

     This means, the set of x with @x<=1 \\/ x=3@ is represented by:
     @x in ]-oo,2[@ and @x not in [2,2]@ and @x in ]2,4[@ and @x not in [4,oo]@

 -}

module CSL.ExtendedParameter where

import qualified Data.Map as Map
import Data.Maybe
import Data.Tree
import Data.List (intercalate)
import Data.Traversable (fmapDefault)

import CSL.AS_BASIC_CSL
--import Common.Lib.Rel
import Common.Id (tokStr)

-- ----------------------------------------------------------------------
-- * Datatypes for efficient Extended Parameter comparison
-- ----------------------------------------------------------------------

-- | Normalized representation of an extended param relation
data NormEP = LeftOf | RightOf | Equal | Except deriving Eq

instance Show NormEP where
    show LeftOf = "<="
    show RightOf = ">="
    show Equal = "="
    show Except = "!="

type EPExp = (NormEP, APInt)

-- | A more efficient representation of a list of extended parameters, 
-- particularly for comparison
type EPExps = Map.Map String EPExp

data Incomparable = Disjoint | Overlap deriving (Eq, Show)

data EPCompare = Comparable Ordering | Incomparable Incomparable deriving Eq

instance Show EPCompare where
    show (Comparable LT) = "<"
    show (Comparable GT) = ">"
    show (Comparable EQ) = "="
    show (Incomparable x) = show x


showEPs :: EPExps -> String
showEPs eps =
    let outp = intercalate ","
               $ map (\ (s, (n, i)) -> s ++ show n ++ show i) $ Map.toList eps
    in if null outp then "*" else outp



-- | Conversion function into the more efficient representation.
toEPExp :: EXTPARAM -> Maybe (String, EPExp)
toEPExp (EP t r i) =
    case r of 
      "<=" -> Just (tokStr t, (LeftOf, i))
      "<" -> Just (tokStr t, (LeftOf, i-1))
      ">=" -> Just (tokStr t, (RightOf, i))
      ">" -> Just (tokStr t, (RightOf, i+1))
      "=" -> Just (tokStr t, (Equal, i))
      "!=" -> Just (tokStr t, (Except, i))
      "-|" -> Nothing
      _ -> error $ "toEPExp: unsupported relation: " ++ r


-- | Conversion function into the more efficient representation.
toEPExps :: [EXTPARAM] -> EPExps
toEPExps = Map.fromList . mapMaybe toEPExp


-- ----------------------------------------------------------------------
-- * Trees to store Extended Parameter indexed values
-- ----------------------------------------------------------------------

{- | We use trees with special labels of this type.


     In two assignments of the same constant we don't allow the
     extended parameter part to overlap. Hence we can store the
     definiens of assignments in a tree indexed by the extended
     parameters. The labels of the tree contain the extended parameter
     and an arbitrary value and all elements in the subforest have a
     label with an extended parameter lower than the extended
     parameter at the root node.

-}
data EPNodeLabel a = EPNL { eplabel :: EPExps
                          , nodelabel :: a }

type EPTree a = Tree (EPNodeLabel a)
type EPForest a = Forest (EPNodeLabel a)

makeEPLeaf :: EPExps -> a -> EPTree a
makeEPLeaf eps x = Node { rootLabel = EPNL { eplabel = eps, nodelabel = x }
                        , subForest = [] }

-- | Inserts a node to an 'EPForest'.
insertEPNodeToForest :: EPTree a -- ^ Node to insert
                     -> EPForest a -- ^ Forest to insert the given node in
                     -> EPForest a -- ^ Resulting forest
insertEPNodeToForest n [] = [n]
insertEPNodeToForest n (t:ft) = case insertEPNode n t of
                                  Just t' -> t': ft
                                  Nothing -> t : insertEPNodeToForest n ft
    

-- | Inserts a node to an 'EPTree' and if the nodes are disjoint
--   'Nothing' is returned. Both insert methods return an error if an
--   overlapping occurs.
insertEPNode :: EPTree a -- ^ Node to insert
             -> EPTree a -- ^ Tree to insert the given node in
             -> Maybe (EPTree a) -- ^ Resulting tree
insertEPNode n t =
    case compareEPs (eplabel $ rootLabel n) $ eplabel $ rootLabel t of
      Comparable EQ -> error "insertEPNode: equality overlap"
      Incomparable Overlap -> error "insertEPNode: overlap"
      Incomparable Disjoint -> Nothing
      Comparable GT -> aInB t n
      Comparable LT -> aInB n t
    where
      aInB a b = Just b { subForest = insertEPNodeToForest a (subForest b) }

-- | Returns a graphical representation of the forest.
showEPForest :: (a -> String) -> EPForest a -> String
showEPForest pr =
    let f lbl = showEPs (eplabel lbl)
                ++ case pr $ nodelabel lbl of
                     [] -> []
                     x -> ": " ++ x
    in drawForest . (map $ fmapDefault f)

-- | This function is not a simple map, but inserts the nodes correctly
-- to the tree.
forestFromEPs :: (a -> EPTree b) -> [a] -> EPForest b
forestFromEPs f l = foldr (insertEPNodeToForest . f) [] l

-- ----------------------------------------------------------------------
-- * Handling of Extended Parameter indexed assignments
-- ----------------------------------------------------------------------

-- | A type to store the different definiens of one constant dependent on the
-- extended parameter range
type AssertionMap = Map.Map String (EPForest EXPRESSION)
-- TODO: implement
-- | Adds a command to the assertionmap. Non-assertion commands are ignored.
insertAssignment :: CMD -> AssertionMap -> AssertionMap
insertAssignment = error "TODO"


-- ----------------------------------------------------------------------
-- * Extended Parameter comparison
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
    

{- | Compares two 'EPExps': They are pairwise compared over the common 
     extended parameter names (see also the operator-table in combineCmp).
     This function can be optimized in returning directly disjoint
     once a disjoint subresult encountered.
-}
compareEPs :: EPExps -> EPExps -> EPCompare
compareEPs eps1 eps2 =
    -- choose smaller map for fold, and remember if maps are swapped
    let (eps, eps', sw) = if Map.size eps1 > Map.size eps2
                          then (eps2, eps1, True) else (eps1, eps2, False)
        -- foldfunction
        f k ep (b, c) = let (cmp', c') = 
                                case Map.lookup k eps' of
                                  -- increment the counter
                                  Just ep' -> (compareEP ep ep', c+1)
                                  -- if key not present in reference map then
                                  -- ep < *
                                  _ -> (Comparable LT, c)
                        in (combineCmp b cmp', c')

        -- we fold over the smaller map, which can be more efficient.
        -- We have to count the number of matched parameter names to see if
        -- there are still EPs in eps' which indicates to compare with ">" at
        -- the end of the fold.
        (epc, cnt) = Map.foldWithKey f
                     (Comparable EQ, 0) -- start the fold with "=",
                                        -- the identity element
                     eps -- the smaller map
        epc' = if Map.size eps' > cnt
               then combineCmp (Comparable GT) epc else epc

    -- if the maps were swapped then swap the result
    in if sw then swapCmp epc' else epc'

-- | Compares two 'EPExp': They are uncompareable if they overlap or are disjoint.
compareEP :: EPExp -> EPExp -> EPCompare
compareEP ep1@(r1, n1) ep2@(r2, n2)
    | r1 == r2 = compareSameRel r1 n1 n2
    | otherwise =
        case (r1, r2) of
          (Equal, Except) | n1 == n2 -> Incomparable Disjoint
                          | otherwise -> Comparable LT
          (Equal, LeftOf) | n1 > n2 -> Incomparable Disjoint
                          | otherwise -> Comparable LT
          (Equal, RightOf) | n1 < n2 -> Incomparable Disjoint
                           | otherwise -> Comparable LT
          (Except, LeftOf) | n1 > n2 -> Comparable GT
                           | otherwise -> Incomparable Overlap
          (Except, RightOf) | n1 < n2 -> Comparable GT
                            | otherwise -> Incomparable Overlap
          (LeftOf, RightOf) | n1 < n2 -> Incomparable Disjoint
                            | otherwise -> Incomparable Overlap
          _ -> swapCmp $ compareEP ep2 ep1


compareSameRel :: NormEP -> APInt -> APInt -> EPCompare
compareSameRel r n1 n2
    | n1 == n2 = Comparable EQ
    | otherwise =
        case r of
          LeftOf -> Comparable (compare n1 n2)
          RightOf -> Comparable (compare n2 n1)
          Equal -> Incomparable Disjoint
          Except -> Incomparable Overlap
