{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2005
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeders@tzi.de
Stability   :  provisional
Portability :  non-portable (cpp)
    

Data.Set and Common.Lib.Set are different types for ghc-6.2.2 but
identical in ghc-6.4

-}

module ATC.Set where

#if __GLASGOW_HASKELL__<=602
import Data.Set
import Common.ATerm.Lib

instance (Ord a, ShATermConvertible a) => ShATermConvertible (Set a) where
    toShATerm att fm = toShATerm att $ setToList fm
    fromShATerm att  = mkSet $ fromShATerm att
#endif
