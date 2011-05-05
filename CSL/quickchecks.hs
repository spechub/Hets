{- |
Module      :  $Header$
Description :  Testing of different parts of the EnCL Implementation
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  portable


Testing using QuickCheck of SetOrdering algos
-}

import Data.List
import qualified Data.Set as Set
import Control.Monad

import Test.QuickCheck
import Test.QuickCheck.Test
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Property
import Test.QuickCheck.Gen

import CSL.TreePO

-- ----------------------------------------------------------------------
-- * Generator for test sets
-- ----------------------------------------------------------------------


diskr = [ ((FinInt 10, True), (PosInf, False))
        , ((FinInt 12, True), (PosInf, False))
        , ((FinInt 10, True), (PosInf, False))
        , ((FinInt 10, True), (PosInf, False))
        , ((FinInt 10, True), (PosInf, False))
        , ((FinInt 10, True), (PosInf, False))
        , ((FinInt 10, True), (PosInf, False))
        , ((FinInt 10, True), (PosInf, False))
        ]
-- data InfInt = PosInf | NegInf | FinInt Integer deriving (Show, Eq)

-- ----------------------------------------------------------------------
-- * Generator for test sets
-- ----------------------------------------------------------------------

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
  let res
          | x == y = IntVal (x, True) (y, True)
          | x > y = IntVal (y, by) (x, bx)
          | otherwise = IntVal (x, bx) (y, by)
  return res

soi :: Gen (SetOrInterval InfInt)
soi = oneof [finset, intval]

comps :: Gen (SetOrInterval InfInt, SetOrInterval InfInt)
comps = do
  soi1 <- soi
  soi2 <- soi
  return (soi1, soi2)


verbCmp (a, b) = do
  putStrLn $ "Compare " ++ show a ++ " and " ++ show b
  putStrLn $ " --> " ++ show (cmpSoIsD a b)


onSmpl g f = do
  l <- smpls g
  mapM_ pr l
      where pr x = do
               putStrLn $ "Input: " ++ show x
               putStrLn $ "  -->  " ++ show (f x)



smpls :: Gen a -> IO [a]
smpls = fmap concat . replicateM 10 . sample'

insts :: Show a => Gen a -> IO ()
insts = replicateM_ 10 . sample

insts' :: Show a => Gen a -> IO ()
insts' g = smpls g >>= writeFile "/tmp/qc" . unlines . map show




newtype Filename = FN { unFN :: String }

instance Show Filename where
    show x = show $ unFN x


instance Arbitrary Filename where
  arbitrary = do name <- elements ["foo", "bar", "baz"]
                 ext <- listOf $ elements ['a'..'z']
                 return (FN (name ++ "." ++ ext))









opt :: Gen String -> Gen String
opt g = oneof [ g, return "" ]

identifier :: Gen String
identifier = do
  i0 <- iden0
  n <- idenN
  return $ i0:n

iden0 :: Gen Char
iden0 = oneof [ elements ['a'..'z'], elements ['A'..'Z']
              , elements ['0'..'9'] ]
idenN :: Gen String
idenN = listOf iden0


filenames :: Gen String
filenames = do
  name <- opt identifier
  dot  <- opt (return ".")
  ext  <- opt identifier
  exts <- listOf identifier
  oneof [ return $ name ++ dot ++ ext
        , return $ name ++ "." ++ (concat . intersperse "." $ exts)]
