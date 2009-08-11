{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Description :  some instances for the Binary class
Copyright   :  (c) DFKI GmbH 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(overlapping Typeable instances)
-}

module Common.BinaryInstances
  ( Binary(..)
  , Put
  , Get
  , putWord8
  , getWord8
  , fromBinaryError
  ) where

import Common.Lib.SizedList as SizedList
import Common.Lib.Rel as Rel
import Common.InjMap as InjMap

import Data.Time (TimeOfDay(..))
import Data.Fixed (Pico)
import Data.Ratio (Ratio)
import System.Time

#ifdef BINARY_PACKAGE
import Data.Binary
#else
import Data.Word

class Binary a where
  put :: a -> Put
  put _ = Nothing
  get :: Get a
  get = Nothing

instance Binary a

type Put = Maybe ()
type Get a = Maybe a

putWord8 :: Word8 -> Put
putWord8 _ = Nothing

getWord8 :: Get Word8
getWord8 = Nothing
#endif

fromBinaryError :: String -> Word8 -> a
fromBinaryError s w = error $ "binary get failed for type '"  ++ s
  ++ "' with variant:" ++ show w

instance Binary a => Binary (SizedList a) where
  put l = put $ SizedList.toList l
  get = do
      l <- get
      return $ SizedList.fromList l

instance (Ord a, Binary a) => Binary (Rel a) where
  put r = put $ Rel.toMap r
  get = do
      m <- get
      return $ Rel.fromDistinctMap m

instance (Ord a, Binary a, Ord b, Binary b) => Binary (InjMap a b) where
  put x = do
        put $ getAToB x
        put $ getBToA x
  get = do
        a <- get
        b <- get
        return $ InjMap.unsafeConstructInjMap a b

instance Binary ClockTime where
  put xv = case xv of
    TOD a b -> do
      put a
      put b
  get = do
      a <- get
      b <- get
      return $ TOD a b

instance Binary TimeOfDay where
  put xv = case xv of
    TimeOfDay a b c -> do
      put a
      put b
      put (toRational c :: Rational)
  get = do
      a <- get
      b <- get
      c <- get
      return $ TimeOfDay a b $ (fromRational :: Ratio Integer -> Pico) c
