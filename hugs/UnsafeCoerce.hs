{- HetCATS/hugs/UnsafeCoerce.hs
   $Id$
   author: Christian Maeder
   year: 2002 

   unsafeCoerce for Hugs
-}

module UnsafeCoerce where

primitive unsafeCoerce "primUnsafeCoerce" :: a -> b