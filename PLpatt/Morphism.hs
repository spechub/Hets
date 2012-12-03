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

data Morphism = Morphism{source :: Sigs,target :: Sigs}
