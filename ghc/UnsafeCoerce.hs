{- HetCATS/ghc/UnsafeCoerce.hs
   $Id$
   author: Christian Maeder
   year: 2002 

   unsafeCoerce for GHC
-}

module UnsafeCoerce where

import GlaExts(unsafeCoerce#)

unsafeCoerce :: a -> b
unsafeCoerce = unsafeCoerce#
