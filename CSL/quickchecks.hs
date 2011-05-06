{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Testing of different parts of the EnCL Implementation
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  portable


Testing using QuickCheck of SetOrdering algos.
Mainly for instance generation of interesting data structures.
-}

import Data.List
import Numeric
import qualified Data.Set as Set
import Control.Monad

import Test.QuickCheck

import CSL.TreePO
import CSL.AS_BASIC_CSL


-- ----------------------------------------------------------------------
-- * Pretty printing
-- ----------------------------------------------------------------------


class Show' a where
    show' :: a -> String

instance Show' a => Show' (SetOrInterval a) where
    show' (Set s) = let l = intersperse "," $ map show' $ Set.toList s
                    in "{" ++ concat l ++ "}"
    show' (IntVal (a, bA) (b, bB)) = let l = if bA then "[" else "]"
                                         r = if bB then "]" else "["
                                     in concat [l, show' a, ", ", show' b, r]

instance Show' a => Show' (CIType a) where
    show' (CIType (x, e)) = case e of
                              Zero -> show' x
                              EpsLeft -> show' x ++ "-"
                              EpsRight -> show' x ++ "+"

instance Show' InfInt where
    show' NegInf = "-oo"
    show' PosInf = "oo"
    show' (FinInt x) = show x

instance Show' a => Show' (Maybe a) where
    show' (Just x) = show' x
    show' Nothing = ""

instance Show' a => Show' (a, a) where
    show' (x,y) = "(" ++ show' x ++ ", " ++ show' y ++ ")"

instance Show' SetOrdering where
    show' = show

instance Show' GroundConstant where
    show' (GCI x) = show x
    show' (GCR x) = show' x

instance Show' APFloat where
    show' x = showFFloat (Just 2) (fromRational x) ""

-- ----------------------------------------------------------------------
-- * Generator for test sets
-- ----------------------------------------------------------------------

gconst :: Gen GroundConstant
gconst = do
  b <- arbitrary
  if b then fmap GCI arbitrary else fmap GCR arbitrary

finborder :: Gen (InfInt, Bool)
finborder = do
  b <- arbitrary
  ii <- fmap FinInt arbitrary
  return (ii, b)

border :: Gen (InfInt, Bool)
border = frequency [ (2, elements [(PosInf, False), (NegInf, False)])
                   , (23, finborder) ]


finset :: Gen (SetOrInterval InfInt)
finset = fmap (Set . Set.fromList . map FinInt) $ listOf1 arbitrary 
-- finset = fmap (Set . Set.map FinInt) arbitrary

intval :: Gen (SetOrInterval InfInt)
intval = do
  (x, bx) <- border
  (y, by) <- border
  let mkRes a ba b bb
          | a == b = IntVal (a, True) (b, True)
          | intsizeA a b == Just 2 && not (ba || bb) = mkRes a (not ba) b bb
          | a > b = IntVal (b, bb) (a, ba)
          | otherwise = IntVal (a, ba) (b, bb)
  return $ mkRes x bx y by



finsetC :: (Ord a) => Gen a -> Gen (SetOrInterval a)
finsetC g = fmap (Set . Set.fromList) $ listOf1 g
-- finset = fmap (Set . Set.map FinInt) arbitrary

intvalC :: (Ord a) => Gen a -> Gen (SetOrInterval a)
intvalC g = do
  x1 <- g
  b1 <- arbitrary
  x2 <- g
  b2 <- arbitrary
  let mkRes a ba b bb
          | a == b = IntVal (a, True) (b, True)
          | a > b = IntVal (b, bb) (a, ba)
          | otherwise = IntVal (a, ba) (b, bb)
  return $ mkRes x1 b1 x2 b2
  

-- main generator functions
soi :: Gen (SetOrInterval InfInt)
soi = oneof [finset, intval]

soiC :: Gen (SetOrInterval GroundConstant)
soiC = oneof [finsetC gconst, intvalC gconst]

comps :: Gen (SetOrInterval InfInt, SetOrInterval InfInt)
comps = do
  soi1 <- soi
  soi2 <- soi
  return (soi1, soi2)

compsC :: Gen (SetOrInterval GroundConstant, SetOrInterval GroundConstant)
compsC = do
  soi1 <- soiC
  soi2 <- soiC
  return (soi1, soi2)




-- run function f on many samples
onSmpl g f = do
  l <- smpls g
  mapM_ pr l
      where pr x = do
               putStrLn $ "Input: " ++ show' x
               putStrLn $ "  -->  " ++ show' (f x)



-- get many samples
smpls :: Gen a -> IO [a]
smpls = fmap concat . replicateM 10 . sample'


-- show samples
insts :: Show a => Gen a -> IO ()
insts = replicateM_ 10 . sample

-- write samples to file
insts' :: Show' a => Gen a -> IO ()
insts' g = smpls g >>= writeFile "/tmp/qc" . unlines . map show'



