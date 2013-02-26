{-
this file is a template for MMT:
basic Morphisms should remain static
-}
module PLpatt.Morphism where

import PLpatt.Sign as Sign
--import qualified Data.Map as Map -- redundant, loaded with Sign
--import qualified PLpatt.AS_BASIC_PLpatt as AS_BASIC -- redundant, loaded with Sign

--data Morphism = Morphism Sign Sign (Map.Map Decl Decl)

--id :: Sign -> Morphism
--id sign = ...

--comp Morphism Morphism
--     Morphism
--comp mor1 mor2 = ... 

{-
idMor :: Sigs -> Morphism
idMor a = inclusionMap a a

inclusionMap :: Sign.Sigs -> Sign.Sigs -> Morphism
inclusionMap s1 s2 = Morphism
  { source = s1
  , target = s2
  , propMap = Map.empty }
-}
data Morphism = Morphism{source :: Sigs,target :: Sigs}
