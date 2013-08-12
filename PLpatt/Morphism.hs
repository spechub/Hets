{-
this file is a template for MMT:
basic Morphisms should remain static
-}
module PLpatt.Morphism where

import PLpatt.Sign as Sign

data Morphism = Morphism{source :: Sigs,target :: Sigs}
