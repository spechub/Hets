{-# OPTIONS -cpp #-}
{-| 
   
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (does -cpp on __GLASGOW_HASKELL__)

   mkAppTy was renamed to mkTyConApp in ghc version 
   6.3 upwards

-}

module Common.DynamicUtils (mkTyConApp) where
import Data.Dynamic

#if __GLASGOW_HASKELL__<=602
mkTyConApp :: TyCon -> [TypeRep] -> TypeRep
mkTyConApp = mkAppTy
#endif
