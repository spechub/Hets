
{- HetCATS/HasCASL/AsUtils.hs
   $Id$
   Authors: Christian Maeder
   Year:    2003
   
   (further) auxiliary functions
-}

module HasCASL.AsUtils where

import HasCASL.As
import Common.Id
import Common.Lib.Set

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
    Intersection is ps -> firstPos (toList is) ps

-- ---------------------------------------------------------------------

posOfVars :: Vars -> Pos
posOfVars vr = 
    case vr of 
    Var v -> posOfId v
    VarTuple vs ps -> firstPos vs ps

instance PosItem Vars where
    get_pos = Just . posOfVars

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
instance PosItem Term where
    get_pos = Just . posOfTerm

posOfTerm :: Term -> Pos
posOfTerm trm =
    case trm of
    CondTerm t1 _ t2 ps -> firstPos [t1, t2] ps
    QualVar v _ ps -> firstPos [v] ps
    QualOp (InstOpId i _ ps) _ qs -> firstPos [i] (ps++qs) 
    ApplTerm t1 t2 ps -> firstPos [t1, t2] ps
    TupleTerm ts ps -> firstPos ts ps 
    TypedTerm t _ _ ps -> firstPos [t] ps 
    QuantifiedTerm _ _ t ps -> firstPos [t] ps 
    LambdaTerm _ _ t ps -> firstPos [t] ps 
    CaseTerm t _ ps -> firstPos [t] ps 
    LetTerm _ t ps -> firstPos [t] ps
    TermToken t -> tokPos t
    MixfixTerm ts -> posOf ts
    BracketTerm _ ts ps -> firstPos ts ps 
