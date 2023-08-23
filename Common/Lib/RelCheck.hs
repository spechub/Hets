{-# LANGUAGE FlexibleInstances #-}
{- |
Module      :  ./Common/Lib/RelCheck.hs
Description :  a couple of test cases mainly for intransKernel
Copyright   :  (c) Uni Bremen 2003-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (Arbitrary instance not of form (T a b c))

a couple of test cases mainly for intransKernel
-}

module Common.Lib.RelCheck where

import Test.QuickCheck
import Common.Lib.Rel
import qualified Common.Lib.MapSet as MapSet

import qualified Data.Map as Map
import qualified Data.Set as Set

instance Arbitrary (Rel Int) where
    arbitrary = do
                   l0 <- arbitrary
                   l1 <- arbitrary
                   l2 <- arbitrary
                   l3 <- arbitrary
                   l4 <- arbitrary
                   let r = fromList (l0 ++ l1 ++ l2 ++ l3 ++ l4)
                       keys = Map.keys $ toMap r
                   x <- choose (0, length keys - 1)
                   y <- choose (0, length keys - 3)
                   z <- choose (0, length keys - 1)
                   x1 <- choose (0, length keys - 2)
                   y1 <- choose (0, length keys - 1)
                   k <- choose (0, length keys - 3)
                   let r' =
                        insertPair x1 y1 $
                        insertPair y1 x1 $
                        insertPair x y $
                        insertPair x z $
                        insertPair z y $
                        insertPair y x $ insertKey k r
                   return r'

prop_IntransKernelTransClosure = prpTransClosure intransKernel

prpTransClosure intrKern r =
     (length (sccOfClosure rel) > 1 &&
     length (Map.keys $ toMap r) > 6) ==>
       classify (Set.size (toSet $ irreflex r) < 10) "trivial"
        (collect (length (Map.keys $ toMap r))
                 (rel == transClosure (intrKern rel)))
    where rel = transClosure r :: Rel Int

tr = transClosure test1

test1 = fromList (zip [(1 :: Int) .. 7] [2 .. 8] ++
                 [(2, 1), (12, 11), (4, 12), (12, 13), (13, 12),
                 (11, 14), (14, 11), (-1, 14), (14, -1), (100, 1), (2, 100)])

test2 = fromList [(1, 2 :: Int), (2, 3), (3, 2), (3, 5), (3, 4), (1, 4), (4, 5),
                  (4, 6), (5, 6), (6, 7), (6, 8), (7, 9), (8, 9)]

test3 = delete 100 1 (test1 `union` fromList (zip [7 .. 100] [8 .. 101]))

test4 = test3 `union` fromList (zip [100 .. 300] [101 .. 301])

test5 = test4 `union` (test2 `union` fromList (zip [301 .. 500] [302, 501]))

test6 = fromList [(2, 1 :: Int), (3, 1), (5, 2), (5, 4), (4, 5), (6, 3), (7, 3)
  , (8, 5), (8, 6), (8, 7), (9, 8), (8, 9), (9, 5), (2, -1), (-11, -10)
  , (-12, -10), (-1, -3)]

test7 = fromList [(2, 1), (3, 1), (4, 2), (5, 2), (6, 3), (7, 6)
  , (8, 6 :: Int), (-7, 7), (7, -7)]

prpEq :: (Rel Int -> Rel Int) -> (Rel Int -> Rel Int) -> Rel Int -> Property
prpEq relFun1 relFun2 rel = let clos = transClosure rel in
    (Set.size (nodes rel) > 6 &&
      clos /= rel && clos /= irreflex clos && transpose rel /= rel) ==>
       classify (Set.size (toSet rel) < 10) "trivial"
        (collect (Set.size (nodes rel))
                (relFun1 rel == relFun2 rel))

prop_irreflexReflexive = prpEq reflexive (reflexive . irreflex . reflexive)

prop_reflexivIrreflex = prpEq irreflex (irreflex . reflexive . irreflex)

prop_TransposeTranspose = prpEq rmNullSets (transpose . transpose)
prop_IrreflexTranspose =
    prpEq (rmNullSets . irreflex . transpose) (transpose . irreflex)
prop_TransClosureTranspose =
    prpEq (transClosure . transpose) (transpose . transClosure)
prop_TransClosureIntransKernel = prpEq (transClosure . irreflex)
    (transClosure . intransKernel . transClosure . irreflex)
