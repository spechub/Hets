
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
	  case get_pos $ head l of 
	  Nothing -> case get_pos_l $ head l of
		     Nothing -> posOf $ tail l
		     Just ps -> if null ps then posOf $ tail l else head ps
	  Just p -> p

firstPos :: PosItem a => [a] -> [Pos] -> Pos
firstPos l ps = if null ps then posOf l else head ps

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
    TypePatternArgs as -> posOf as
-- ---------------------------------------------------------------------

instance PosItem TypeArgs where
    get_pos (TypeArgs tArgs ps) = Just $ firstPos tArgs ps

instance PosItem TypeScheme where
    get_pos (TypeScheme tArgs _ ps) = Just $ firstPos tArgs ps

instance PosItem Type where
    get_pos = Just . posOfType

posOfType :: Type -> Pos
posOfType ty = 
    case ty of
    TypeName i _ -> posOfId i
    TypeAppl t1 t2 -> posOf [t1, t2]
    TypeToken t -> tokPos t
    BracketType _ ts ps -> firstPos ts ps
    KindedType t _ ps -> firstPos [t] ps
    MixfixType ts -> posOf ts
    LazyType t ps -> firstPos [t] ps
    ProductType ts ps -> firstPos ts ps
    FunType t1 _ t2 ps -> firstPos [t1,t2] ps

-- ---------------------------------------------------------------------
