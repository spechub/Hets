{-# OPTIONS -cpp #-}
{-|

Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable (does -cpp on __GLASGOW_HASKELL__)

mkAppTy was renamed to mkTyConApp in ghc version 6.3 upwards
-}

module Common.DynamicUtils (mkTyConApp, mkTyCon, TyCon, Typeable(..)) where

import Data.Typeable

#if __GLASGOW_HASKELL__<=602
import Data.Dynamic

mkTyConApp :: TyCon -> [TypeRep] -> TypeRep
mkTyConApp = mkAppTy
#endif
