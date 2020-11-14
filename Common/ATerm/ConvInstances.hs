{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable #-}
{- |
Module      :  ./Common/ATerm/ConvInstances.hs
Description :  special ShATermConvertible instances
Copyright   :  (c) Klaus Luettich, C. Maeder, Uni Bremen 2005-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (overlapping Typeable instances)

This module provides instances of `ShATermConvertible`.
-}

module Common.ATerm.ConvInstances () where

import ATerm.Lib
import Common.Lib.SizedList as SizedList
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet
import qualified Common.InjMap as InjMap
import Data.Typeable
import Data.Time (TimeOfDay (..))
import Data.Fixed (Pico)
import Data.Ratio (Ratio)
import System.Time
import Data.Hashable
import qualified Data.HashMap.Strict as Map
import qualified Data.HashSet as Set

instance ShATermConvertible a => ShATermConvertible (SizedList.SizedList a)
    where
  toShATermAux att0 = toShATermAux att0 . SizedList.toList
  fromShATermAux ix att0 = case fromShATermAux ix att0 of
    (att, l) -> (att, SizedList.fromList l)

instance (Ord a, ShATermConvertible a, Ord b, ShATermConvertible b)
     => ShATermConvertible (InjMap.InjMap a b) where
  toShATermAux att0 x = do
        (att1, a') <- toShATerm' att0 $ InjMap.getAToB x
        (att2, b') <- toShATerm' att1 $ InjMap.getBToA x
        return $ addATerm (ShAAppl "InjMap" [a', b'] []) att2
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "InjMap" [a, b] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        (att2, InjMap.unsafeConstructInjMap a' b') }}
    u -> fromShATermError "InjMap" u

-- TODO: get this right!
instance (Ord a, Hashable a, Typeable a, Typeable b)--, ShATermConvertible a, ShATermConvertible b)
 => ShATermConvertible (Map.HashMap a b) where
   toShATermAux att0 x = error "nyi"--toShATermAux att0 $ Map.toList x
   fromShATermAux ix att0 = error "nyi"--fromShATermError "HashMap" $ getShATerm ix att0

instance (Ord a, Hashable a, Typeable a) =>
         ShATermConvertible (Set.HashSet a) where
   toShATermAux att0 x = error "nyi"--toShATermAux att0 $ Map.toList x
   fromShATermAux ix att0 = error "nyi"--fromShATermError "HashMap" $ getShATerm ix att0 

instance (Ord a, Hashable a, ShATermConvertible a, Ord b, Hashable b, ShATermConvertible b)
  => ShATermConvertible (MapSet.MapSet a b) where
  toShATermAux att0 r = do
        (att1, a') <- toShATerm' att0 $ MapSet.toMap r
        return $ addATerm (ShAAppl "MapSet" [a'] []) att1
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "MapSet" [a] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        (att1, MapSet.fromDistinctMap a') }
    u -> fromShATermError "MapSet" u

instance (Ord a, Hashable a, ShATermConvertible a) => ShATermConvertible (Rel.Rel a) where
  toShATermAux att0 r = do
        (att1, a') <- toShATerm' att0 $ Rel.toMap r
        return $ addATerm (ShAAppl "Rel" [a'] []) att1
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "Rel" [a] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        (att1, Rel.fromMap a') }
    u -> fromShATermError "Rel" u

deriving instance Typeable ClockTime

instance ShATermConvertible ClockTime where
    toShATermAux att0 (TOD a b) = do
        (att1, a') <- toShATerm' att0 a
        (att2, b') <- toShATerm' att1 b
        return $ addATerm (ShAAppl "TOD" [a', b'] []) att2
    fromShATermAux ix att0 = case getShATerm ix att0 of
            ShAAppl "TOD" [a, b] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    case fromShATerm' b att1 of { (att2, b') ->
                    (att2, TOD a' b') }}
            u -> fromShATermError "ClockTime" u

instance ShATermConvertible Double where
    toShATermAux att = toShATermAux att . toRational
    fromShATermAux ix att0 = case fromShATermAux ix att0 of
       (att, r) -> (att, fromRational r)

instance ShATermConvertible TimeOfDay where
    toShATermAux att0 (TimeOfDay a b c) = do
        (att1, a') <- toShATerm' att0 a
        (att2, b') <- toShATerm' att1 b
        (att3, c') <- toShATerm' att2 (toRational c :: Rational)
        return $ addATerm (ShAAppl "TimeOfDay" [a', b', c'] []) att3
    fromShATermAux ix att0 = case getShATerm ix att0 of
            ShAAppl "TimeOfDay" [a, b, c] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    case fromShATerm' b att1 of { (att2, b') ->
                    case fromShATerm' c att2 of { (att3, c') ->
                    (att3, TimeOfDay a' b'
                     $ (fromRational :: Ratio Integer -> Pico) c') }}}
            u -> fromShATermError "TimeOfDay" u

instance ShATermConvertible Ordering where
    toShATermAux att = toShATermAux att . ordToInt
    fromShATermAux ix att0 = case fromShATermAux ix att0 of
       (att, i) -> (att, ordFromInt i)

ordFromInt :: Int -> Ordering
ordFromInt 0 = LT
ordFromInt 1 = EQ
ordFromInt 2 = GT
ordFromInt i = error $ "ordFromInt: only values from 0 to 2 allowed but got "
               ++ show i

ordToInt :: Ordering -> Int
ordToInt LT = 0
ordToInt EQ = 1
ordToInt GT = 2
