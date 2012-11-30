module <LogicName>.Morphism where

import <LogicName>.Sign as Sign
import qualified Data.Map as Map
import qualified <LogicName>.AS_BASIC_<LogicName> as AS_BASIC

--data Morphism = Morphism Sign Sign (Map.Map Decl Decl)

id :: Sign -> Morphism
id sign = ...

comp Morphism Morphism
     Morphism
comp mor1 mor2 = ... 

<insert>
