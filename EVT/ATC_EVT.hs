{-# OPTIONS -w -O0 #-}
{- |
Module      :  EVT/ATC_EVT.der.hs
Description :  generated ShATermConvertible instances
Copyright   :  (c) DFKI GmbH 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(derive Typeable instances)

Automatic derivation of instances via DrIFT-rule ShATermConvertible
  for the type(s):
'EVT.AS.MACHINE'
'EVT.AS.EVENT'
'EVT.AS.GUARD'
'EVT.AS.ACTION'
'EVT.AS.EVTQualId'
'EVT.Sign.EVTSign'
'EVT.Sign.EVTMorphism'
'EVT.Sign.EVTDatatype'
'EVT.Sign.EVTSymbol'
-}

{-
Generated by 'genRules' (automatic rule generation for DrIFT). Don't touch!!
  dependency files:
EVT/AS.hs
EVT/Sign.hs
-}

module EVT.ATC_EVT () where

import ATC.GlobalAnnotations
import ATerm.Lib
import CASL.AS_Basic_CASL
import CASL.ATC_CASL ()
import Common.Id
import Data.Data
import EVT.AS
import EVT.Sign
import qualified Data.Map as Map

{-! for EVT.AS.MACHINE derive : ShATermConvertible !-}
{-! for EVT.AS.EVENT derive : ShATermConvertible !-}
{-! for EVT.AS.GUARD derive : ShATermConvertible !-}
{-! for EVT.AS.ACTION derive : ShATermConvertible !-}
{-! for EVT.AS.EVTQualId derive : ShATermConvertible !-}
{-! for EVT.Sign.EVTSign derive : ShATermConvertible !-}
{-! for EVT.Sign.EVTMorphism derive : ShATermConvertible !-}
{-! for EVT.Sign.EVTDatatype derive : ShATermConvertible !-}
{-! for EVT.Sign.EVTSymbol derive : ShATermConvertible !-}

-- Generated by DrIFT, look but don't touch!

instance ShATermConvertible MACHINE where
  toShATermAux att0 xv = case xv of
    MACHINE a -> do
      (att1, a') <- toShATerm' att0 a
      return $ addATerm (ShAAppl "MACHINE" [a'] []) att1
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "MACHINE" [a] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      (att1, MACHINE a') }
    u -> fromShATermError "MACHINE" u

instance ShATermConvertible EVENT where
  toShATermAux att0 xv = case xv of
    EVENT a b c -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      (att3, c') <- toShATerm' att2 c
      return $ addATerm (ShAAppl "EVENT" [a', b', c'] []) att3
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "EVENT" [a, b, c] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      case fromShATerm' c att2 of
      { (att3, c') ->
      (att3, EVENT a' b' c') }}}
    u -> fromShATermError "EVENT" u

instance ShATermConvertible GUARD where
  toShATermAux att0 xv = case xv of
    GUARD a b -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      return $ addATerm (ShAAppl "GUARD" [a', b'] []) att2
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "GUARD" [a, b] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      (att2, GUARD a' b') }}
    u -> fromShATermError "GUARD" u

instance ShATermConvertible ACTION where
  toShATermAux att0 xv = case xv of
    ACTION a b -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      return $ addATerm (ShAAppl "ACTION" [a', b'] []) att2
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "ACTION" [a, b] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      (att2, ACTION a' b') }}
    u -> fromShATermError "ACTION" u

instance ShATermConvertible EVTQualId where
  toShATermAux att0 xv = case xv of
    EVTQualId a -> do
      (att1, a') <- toShATerm' att0 a
      return $ addATerm (ShAAppl "EVTQualId" [a'] []) att1
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "EVTQualId" [a] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      (att1, EVTQualId a') }
    u -> fromShATermError "EVTQualId" u

instance ShATermConvertible EVTSymbol where
  toShATermAux att0 xv = case xv of
    E a -> do
      (att1, a') <- toShATerm' att0 a
      return $ addATerm (ShAAppl "E" [a'] []) att1
    EVTDatatype a -> do
      (att1, a') <- toShATerm' att0 a
      return $ addATerm (ShAAppl "EVTDatatype" [a'] []) att1
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "E" [a] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      (att1, E a') }
    ShAAppl "EVTDatatype" [a] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      (att1, EVTDatatype a') }
    u -> fromShATermError "EVTSymbol" u

instance ShATermConvertible EVTDatatype where
  toShATermAux att0 xv = case xv of
    EVTBoolean -> return $ addATerm (ShAAppl "EVTBoolean" [] []) att0
    EVTNat -> return $ addATerm (ShAAppl "EVTNat" [] []) att0
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "EVTBoolean" [] _ -> (att0, EVTBoolean)
    ShAAppl "EVTNat" [] _ -> (att0, EVTNat)
    u -> fromShATermError "EVTDatatype" u

instance ShATermConvertible EVTMorphism where
  toShATermAux att0 xv = case xv of
    EVTMorphism a b c -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      (att3, c') <- toShATerm' att2 c
      return $ addATerm (ShAAppl "EVTMorphism" [a', b', c'] []) att3
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "EVTMorphism" [a, b, c] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      case fromShATerm' c att2 of
      { (att3, c') ->
      (att3, EVTMorphism a' b' c') }}}
    u -> fromShATermError "EVTMorphism" u

instance ShATermConvertible EVTSign where
  toShATermAux att0 xv = case xv of
    EVTSign a b -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      return $ addATerm (ShAAppl "EVTSign" [a', b'] []) att2
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "EVTSign" [a, b] _ ->
      case fromShATerm' a att0 of
      { (att1, a') ->
      case fromShATerm' b att1 of
      { (att2, b') ->
      (att2, EVTSign a' b') }}
    u -> fromShATermError "EVTSign" u
