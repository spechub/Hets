{-| 
   
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Utilities for Data.Dynamic

-}

module Common.DynamicUtils where
import Data.Dynamic

mkTyConApp :: TyCon -> [TypeRep] -> TypeRep
mkTyConApp = mkAppTy
