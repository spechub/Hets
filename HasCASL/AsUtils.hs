
{- HetCATS/HasCASL/AsUtils.hs
   $Id$
   Authors: Christian Maeder
   Year:    2003
   
   (further) auxiliary functions
-}

module AsUtils where

import As
import Id

-- ---------------------------------------------------------------------

kindArity :: Kind -> Int
kindArity(Kind args _ _) = 
    sum $ map prodClassArity args

prodClassArity :: ProdClass -> Int
prodClassArity (ProdClass l _) = length l

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
       let TypeArg t _ _ _ = head as in tokPos t



