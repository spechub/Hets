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
import Data.Ratio
import System.Time

#ifdef BINARY_PACKAGE
import Data.Binary
#else
import Control.Monad
import Data.Char
import Data.Word
import Data.List as List
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set

import qualified Common.Lib.State as State

type Put = State.State [Word8] ()
type Get a = State.State [Word8] a

putWord8 :: Word8 -> Put
putWord8 w = State.modify (w :)

getWord8 :: Get Word8
getWord8 = do
  l <- State.get
  case l of
    w : r -> do
      State.put r
      return w
    [] -> error "getWord8"

-- partly copied from the Data/Binary.hs
class Binary a where
  put :: a -> Put
  get :: Get a

instance Binary () where
    put ()  = return ()
    get     = return ()

instance Binary Bool where
    put     = putWord8 . fromIntegral . fromEnum
    get     = liftM (toEnum . fromIntegral) getWord8

instance Binary Char where
    put = putWord8 . fromIntegral . ord
    get = fmap (chr . fromIntegral) getWord8

instance Binary Word8 where
    put     = putWord8
    get     = getWord8

instance Binary Float where
    put     = put . show
    get     = fmap read get

instance Binary Int where
    put     = put . show
    get     = fmap read get

instance Binary Integer where
    put     = put . show
    get     = fmap read get

instance (Binary a, Integral a) => Binary (Ratio a) where
    put i = do
      put $ numerator i
      put $ denominator i
    get = do
      a <- get
      b <- get
      return $ a % b

instance (Binary a, Binary b) => Binary (a,b) where
    put (a,b)           = put a >> put b
    get                 = liftM2 (,) get get

instance (Binary a, Binary b, Binary c) => Binary (a,b,c) where
    put (a,b,c)         = put a >> put b >> put c
    get                 = liftM3 (,,) get get get

instance (Binary a, Binary b, Binary c, Binary d) => Binary (a,b,c,d) where
    put (a,b,c,d)       = put a >> put b >> put c >> put d
    get                 = liftM4 (,,,) get get get get

instance Binary a => Binary [a] where
    put l  = put (length l) >> mapM_ put l
    get    = do n <- get :: Get Int
                getMany n

-- | 'getMany n' get 'n' elements in order, without blowing the stack.
getMany :: Binary a => Int -> Get [a]
getMany n = go [] n
 where
    go xs 0 = return $! List.reverse xs
    go xs i = do x <- get
                 -- we must seq x to avoid stack overflows due to laziness in
                 -- (>>=)
                 x `seq` go (x:xs) (i-1)
{-# INLINE getMany #-}

instance (Binary a) => Binary (Maybe a) where
    put Nothing  = putWord8 0
    put (Just x) = putWord8 1 >> put x
    get = do
        w <- getWord8
        case w of
            0 -> return Nothing
            _ -> liftM Just get

instance (Binary a, Binary b) => Binary (Either a b) where
    put (Left  a) = putWord8 0 >> put a
    put (Right b) = putWord8 1 >> put b
    get = do
        w <- getWord8
        case w of
            0 -> liftM Left  get
            _ -> liftM Right get

instance (Ord a, Binary a) => Binary (Set.Set a) where
    put s = put (Set.size s) >> mapM_ put (Set.toAscList s)
    get   = liftM Set.fromDistinctAscList get

instance (Ord k, Binary k, Binary e) => Binary (Map.Map k e) where
    put m = put (Map.size m) >> mapM_ put (Map.toAscList m)
    get   = liftM Map.fromDistinctAscList get

instance (Binary e) => Binary (IntMap.IntMap e) where
    put m = put (IntMap.size m) >> mapM_ put (IntMap.toAscList m)
    get   = liftM IntMap.fromDistinctAscList get
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
