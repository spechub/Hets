{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003 
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 
   
   compute meaningful positions for various data types of the abstract syntax
-}

module HasCASL.AsUtils where

import HasCASL.As
import HasCASL.PrintAs -- to reexport instances
import Common.Id
import Common.Lib.Set
import Common.PrettyPrint

-- | generate a comparison string 
expected :: PrettyPrint a => a -> a -> String
expected a b = 
    "\n  expected: " ++ showPretty a 
    "\n     found: " ++ showPretty b "\n" 

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
    QualVar v _ ps -> firstPos [v] ps
    QualOp (InstOpId i _ ps) _ qs -> firstPos [i] (ps++qs) 
    ResolvedMixTerm i _ _ -> posOfId i
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

-- ---------------------------------------------------------------------
instance PosItem Pattern where
    get_pos = Just . posOfPat

posOfPat :: Pattern -> Pos
posOfPat pat =
    case pat of
    PatternVar vs -> getMyPos vs
    ResolvedMixPattern i _ _ -> posOfId i
    PatternConstr (InstOpId i _ _) _ _ qs -> firstPos [i] qs
    PatternToken t -> tokPos t
    BracketPattern _ ps qs -> firstPos ps qs
    TuplePattern ps qs -> firstPos ps qs
    MixfixPattern ps -> posOf ps
    TypedPattern p _ ps -> firstPos [p] ps
    AsPattern p1 p2 ps -> firstPos [p1, p2] ps

instance PosItem VarDecl where
    get_pos (VarDecl v _ _ ps) = Just $ firstPos [v] ps
