{-# LANGUAGE CPP #-}
{- |
Module      :  $Header$
Description :  special ShATermConvertible instances
Copyright   :  (c) Klaus Luettich, C. Maeder, Uni Bremen 2005-2006
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (overlapping Typeable instances)

This module provides instances of `ShATermConvertible`.
-}

module Common.ATerm.ConvInstances () where

import ATerm.Lib
import Common.Lib.SizedList as SizedList
import qualified Common.Lib.Rel as Rel
import qualified Common.InjMap as InjMap
import Data.Typeable
import Data.Time (TimeOfDay(..))
import Data.Fixed (Pico)
import Data.Ratio (Ratio)
import System.Time

_tc_SizedListTc :: TyCon
_tc_SizedListTc = mkTyCon "Common.Lib.SizedList.SizedList"
instance Typeable1 SizedList where
    typeOf1 _ = mkTyConApp _tc_SizedListTc []

instance ShATermConvertible a => ShATermConvertible (SizedList.SizedList a)
    where
  toShATermAux att0 = toShATermAux att0 . SizedList.toList
  fromShATermAux ix att0 = case fromShATermAux ix att0 of
    (att, l) -> (att, SizedList.fromList l)

_tc_InjMapTc :: TyCon
_tc_InjMapTc = mkTyCon "Common.InjMap.InjMap"
instance Typeable2 InjMap.InjMap where
    typeOf2 _ = mkTyConApp _tc_InjMapTc []

instance (Ord a, ShATermConvertible a, Ord b, ShATermConvertible b)
     => ShATermConvertible (InjMap.InjMap a b) where
  toShATermAux att0 x = do
        (att1, a') <- toShATerm' att0 $ InjMap.getAToB x
        (att2, b') <- toShATerm' att1 $ InjMap.getBToA x
        return $ addATerm (ShAAppl "InjMap" [a',b'] []) att2
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "InjMap" [a,b] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        case fromShATerm' b att1 of { (att2, b') ->
        (att2, InjMap.unsafeConstructInjMap a' b') }}
    u -> fromShATermError "InjMap" u

_tc_RelTc :: TyCon
_tc_RelTc = mkTyCon "Common.Lib.Rel.Rel"
instance Typeable1 Rel.Rel where
    typeOf1 _ = mkTyConApp _tc_RelTc []

instance (Ord a, ShATermConvertible a) => ShATermConvertible (Rel.Rel a) where
  toShATermAux att0 r = do
        (att1, a') <- toShATerm' att0 $ Rel.toMap r
        return $ addATerm (ShAAppl "Rel" [a'] []) att1
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "Rel" [a] _ ->
        case fromShATerm' a att0 of { (att1, a') ->
        (att1, Rel.fromDistinctMap a') }
    u -> fromShATermError "Rel" u

ctTc :: TyCon
ctTc = mkTyCon "System.Time.ClockTime"

instance Typeable ClockTime where
  typeOf _ = mkTyConApp ctTc []

instance ShATermConvertible ClockTime where
    toShATermAux att0 (TOD a b) = do
        (att1, a') <- toShATerm' att0 a
        (att2, b') <- toShATerm' att1 b
        return $ addATerm (ShAAppl "TOD" [a',b'] []) att2
    fromShATermAux ix att0 = case getShATerm ix att0 of
            ShAAppl "TOD" [a,b] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    case fromShATerm' b att1 of { (att2, b') ->
                    (att2, TOD a' b') }}
            u -> fromShATermError "ClockTime" u

#ifdef TIME_WITHOUT_TYPEABLE
timeOfDayTc :: TyCon
timeOfDayTc = mkTyCon "Data.Time.TimeOfDay"

instance Typeable TimeOfDay where
    typeOf _ = mkTyConApp timeOfDayTc []
#endif

instance ShATermConvertible TimeOfDay where
    toShATermAux att0 (TimeOfDay a b c) = do
        (att1, a') <- toShATerm' att0 a
        (att2, b') <- toShATerm' att1 b
        (att3, c') <- toShATerm' att2 (toRational c :: Rational)
        return $ addATerm (ShAAppl "TimeOfDay" [a',b',c'] []) att3
    fromShATermAux ix att0 = case getShATerm ix att0 of
            ShAAppl "TimeOfDay" [a,b,c] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    case fromShATerm' b att1 of { (att2, b') ->
                    case fromShATerm' c att2 of { (att3, c') ->
                    (att3, TimeOfDay a' b'
                     $ (fromRational :: Ratio Integer -> Pico) c') }}}
            u -> fromShATermError "TimeOfDay" u
