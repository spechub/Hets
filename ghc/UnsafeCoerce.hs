{- HetCATS/ghc/UnsafeCoerce.hs
   $Id$
   author: Christian Maeder
   year: 2002 

   unsafeCoerce for GHC
-}

module UnsafeCoerce where

import GHC.Exts(unsafeCoerce#)

unsafeCoerce :: a -> b
unsafeCoerce = unsafeCoerce#
