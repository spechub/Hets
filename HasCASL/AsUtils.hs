
{- HetCATS/HasCASL/AsUtils.hs
   $Id$
   Authors: Christian Maeder
   Year:    2003
   
   (further) auxiliary functions
-}

module AsUtils where

import As
import Id

posOfKind :: Kind -> Pos
posOfKind (KindAppl _ _ p) = p 
posOfKind (ProdClass _ ps) = head ps
posOfKind (ExtClass _ _ p) = p
posOfKind (PlainClass c) = posOfClass c

posOfClass :: Class -> Pos 
posOfClass (Downset t) = posOfType t
posOfClass (Intersection is ps) = 
    if null ps then if null is then nullPos else posOfId $ head is
       else head ps
-- ---------------------------------------------------------------------

posOfTypePattern :: TypePattern -> Pos
posOfTypePattern (TypePattern t _ _) = posOfId t
posOfTypePattern (TypePatternToken t) = tokPos t
posOfTypePattern (MixfixTypePattern ts) = 
    if null ts then nullPos else posOfTypePattern $ head ts
posOfTypePattern (BracketTypePattern _ ts ps) = 
    if null ps then 
       if null ts then nullPos
       else posOfTypePattern $ head ts
    else head ps
posOfTypePattern (TypePatternArgs as) = 
    if null as then nullPos else 
       let TypeArg t _ _ _ = head as in posOfId t

-- ---------------------------------------------------------------------

posOfType :: Type -> Pos
posOfType (TypeName i _) = posOfId i
posOfType (TypeAppl _ t2) = posOfType t2
posOfType (TypeToken t) = tokPos t
posOfType (BracketType _ ts ps) = 
    if null ps then 
       if null ts then nullPos else posOfType $ head ts 
    else head ps
posOfType (KindedType t _ p) = if p == nullPos then posOfType t else p
posOfType (MixfixType ts) = if null ts then nullPos else posOfType $ head ts
posOfType (LazyType t p) = if p == nullPos then posOfType t else p
posOfType (ProductType ts ps) = 
    if null ps then 
       if null ts then nullPos else posOfType $ head ts 
    else head ps
posOfType (FunType t _ _ ps) = 
    if null ps then posOfType t else head ps

