{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
{- |
Module      :  $Header$
Description :  Handling of extended parameters
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  non-portable

This module defines an ordering on extended parameters and other analysis tools
-}

module CSL.ExtendedParameters where

import qualified Data.Map as Map

import CSL.AS_BASIC_CSL
--import Common.Lib.Rel

-- ----------------------------------------------------------------------
-- * Datatypes for efficient Extended Parameter comparison
-- ----------------------------------------------------------------------

-- data EXTPARAM = EP Id.Token String (Maybe EXPRESSION)

-- | Normalized representation of an extended param relation
data NormEP = LeftOf | RightOf | Equal | Except deriving Eq

{- | Extended parameters may be based on one of the following relations:
     =, <=, >=, !=, <, >, -|

     We reduce the relations to one of the Data items in NormEP.
     We handle -| as * for comparison and range computations, i.e., we remove
     it, and < n is turned into <= n-1 (or LeftOf n-1) and accordingly for > .
-}
type EPExp = (NormEP, APInt)


-- | A more efficient representation of a list of extended parameters, 
-- particularly for comparison
type EPExps = Map.Map String (NormEP, APInt)

data Incomparable = Disjoint | Overlap

type EPCompare = Either Incomparable Ordering

isLeft :: NormEP -> Bool
isLeft LeftOf = True
isLeft _ = False

isRight :: NormEP -> Bool
isRight RightOf = True
isRight _ = False

isEqual :: NormEP -> Bool
isEqual Equal = True
isEqual _ = False

isExcept :: NormEP -> Bool
isExcept Except = True
isExcept _ = False

swapCmp :: EPCompare -> EPCompare
swapCmp (Right LT) = (Right GT)
swapCmp (Right GT) = (Right LT)
swapCmp x = x

compareSameRel :: NormEP -> APInt -> APInt -> EPCompare
compareSameRel r n1 n2
    | n1 == n2 = Right EQ
    | otherwise =
        case r of
          LeftOf -> Right (compare n1 n2)
          RightOf -> Right (compare n2 n1)
          Equal -> Left Disjoint
          Except -> Left Overlap

{- | We combine the comparison outcome of the individual parameters with
     the following (symmetrical) table:

     \ > < = O D
     > > O > O D
     <   < < O D
     =     = O D
     O       O D
     D         D
    


compareEP :: EPExps -> EPExps -> EPCompare
compareEP eps1 eps2 =
    let (eps, eps') = if Map.size eps1 > Map.size eps2
                       then (eps2, eps1) else (eps1, eps2)
-}

-- | Compares two EPExp: The are uncompareable if the overlap or are disjoint
compareEP :: EPExp -> EPExp -> EPCompare
compareEP ep1@(r1, n1) ep2@(r2, n2)
    | r1 == r2 = compareSameRel r1 n1 n2
    | otherwise =
        case (r1, r2) of
          (Equal, Except) | n1 == n2 -> Left Disjoint
                          | otherwise -> Right LT
          (Equal, _) -> Right LT
          (Except, LeftOf) | n1 > n2 -> Right GT
                           | otherwise -> Left Overlap
          (Except, RightOf) | n2 > n1 -> Right GT
                            | otherwise -> Left Overlap
          (LeftOf, RightOf) | n1 < n2 -> Left Disjoint
                            | otherwise -> Left Overlap
          _ -> swapCmp $ compareEP ep2 ep1

