{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   unsafeCoerce for Hugs
-}

module UnsafeCoerce where

primitive unsafeCoerce "primUnsafeCoerce" :: a -> b
