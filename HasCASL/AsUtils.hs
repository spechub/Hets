
{- HetCATS/HasCASL/AsUtils.hs
   $Id$
   Authors: Christian Maeder
   Year:    2003
   
   (further) auxiliary functions
-}

module HasCASL.AsUtils where

import HasCASL.As
import Common.Id

posOf :: PosItem a => [a] -> Pos
posOf l = if null l then nullPos else 
	  let q = case get_pos_l $ head l of
		     Nothing -> posOf $ tail l
		     Just ps -> let p = getPos ps in 
					if p == nullPos 
					   then posOf $ tail l else p in
	  case get_pos $ head l of 
	  Nothing -> q
	  Just p -> if p == nullPos then q else p

firstPos :: PosItem a => [a] -> [Pos] -> Pos
firstPos l ps = let p = posOf l in 
			if p == nullPos then getPos ps else p

getPos :: [Pos] -> Pos
getPos [] = nullPos
getPos (a:r) = if a == nullPos then getPos r else a  

instance PosItem Kind where
    get_pos = Just . posOfKind

posOfKind :: Kind -> Pos
posOfKind k = 
    case k of 
    KindAppl k1 k2 ps -> firstPos [k1,k2] ps 
    ExtClass c _ ps -> firstPos [c] ps

instance PosItem Class where
    get_pos = Just . posOfClass

posOfClass :: Class -> Pos 
posOfClass c = 
    case c of
    Downset t -> posOfType t
    Intersection is ps -> firstPos is ps

-- ---------------------------------------------------------------------
instance PosItem TypePattern where
    get_pos = Just . posOfTypePattern

instance PosItem TypeArg where
    get_pos (TypeArg t _ _ _) = Just $ posOfId t

posOfTypePattern :: TypePattern -> Pos
posOfTypePattern pat = 
    case pat of
    TypePattern t _ _ -> posOfId t
    TypePatternToken t -> tokPos t
    MixfixTypePattern ts -> posOf ts
    BracketTypePattern _ ts ps -> firstPos ts ps
    TypePatternArg (TypeArg t _ _ _) _ -> posOfId t
-- ---------------------------------------------------------------------

instance PosItem TypeScheme where
    get_pos (TypeScheme tArgs _ ps) = Just $ firstPos tArgs ps

instance PosItem Type where
    get_pos = Just . posOfType

posOfType :: Type -> Pos
posOfType ty = 
    case ty of
    TypeName i _ _ -> posOfId i
    TypeAppl t1 t2 -> posOf [t1, t2]
    TypeToken t -> tokPos t
    BracketType _ ts ps -> firstPos ts ps
    KindedType t _ ps -> firstPos [t] ps
    MixfixType ts -> posOf ts
    LazyType t ps -> firstPos [t] ps
    ProductType ts ps -> firstPos ts ps
    FunType t1 _ t2 ps -> firstPos [t1,t2] ps

-- ---------------------------------------------------------------------
