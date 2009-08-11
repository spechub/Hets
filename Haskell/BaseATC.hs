{- |
Module      :  $Header$
Description :  basic ShATermConvertible instances
Copyright   :  (c) Christian Maeder, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

a few basic 'ShATermConvertible' instances needed by "Haskell.ATC_Haskell"
-}

module Haskell.BaseATC () where

import Common.ATerm.Lib
import Data.Typeable
import SrcLoc

_tcSrcLocTc :: TyCon
_tcSrcLocTc = mkTyCon "SrcLoc.SrcLoc"
instance Typeable SrcLoc where
    typeOf _ = mkTyConApp _tcSrcLocTc []

instance ShATermConvertible SrcLoc where
  toShATermAux att0 xv = case xv of
    SrcLoc a b c d -> do
      (att1, a') <- toShATerm' att0 a
      (att2, b') <- toShATerm' att1 b
      (att3, c') <- toShATerm' att2 c
      (att4, d') <- toShATerm' att3 d
      return $ addATerm (ShAAppl "SrcLoc" [a',b',c',d'] []) att4
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "SrcLoc" [a,b,c,d] _ ->
      case fromShATerm' a att0 of { (att1, a') ->
      case fromShATerm' b att1 of { (att2, b') ->
      case fromShATerm' c att2 of { (att3, c') ->
      case fromShATerm' d att3 of { (att4, d') ->
      (att4, SrcLoc a' b' c' d') }}}}
    u -> fromShATermError "SrcLoc" u
