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
    toShATermAux att set = do
      (att1, i) <-  toShATerm' att $ setToList set
      return $ addATerm (ShAAppl "DataSet" [i] []) att1
    fromShATermAux ix att0 =
        case getShATerm ix att0 of
            ShAAppl "DataSet" [a] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    (att1, mkSet a') }
            u -> fromShATermError "Data.Set.Set" u
#endif
