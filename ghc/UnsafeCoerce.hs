{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   unsafeCoerce for GHC
-}

module UnsafeCoerce where

import GHC.Exts(unsafeCoerce#)

unsafeCoerce :: a -> b
unsafeCoerce = unsafeCoerce#
