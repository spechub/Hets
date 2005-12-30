{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeders@tzi.de
Stability   :  provisional
Portability :  non-portable (cpp)

Data.Set and Common.Lib.Set are different types for ghc-6.2.2 but
identical in ghc-6.4
-}

module ATC.Set() where

#if __GLASGOW_HASKELL__<=602
import Data.Set
import Common.ATerm.Lib
import Common.DynamicUtils

setTc :: TyCon
setTc = mkTyCon "Data.Set.Set"

instance Typeable a => Typeable (Set a) where
  typeOf s = mkTyConApp setTc [typeOf ((undefined:: Set a -> a) s)]

instance (Ord a, ShATermConvertible a) => ShATermConvertible (Set a) where
    toShATerm att fm = toShATerm att $ setToList fm
    fromShATerm att  = mkSet $ fromShATerm att
#endif
