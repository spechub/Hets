{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003 
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 
   
   compute meaningful positions for various data types of the abstract syntax
-}

module HasCASL.AsUtils where

import HasCASL.As
import HasCASL.PrintAs -- to reexport instances
import Common.Id
import Common.PrettyPrint

-- | extract bindings from an analysed pattern
extractVars :: Pattern -> [VarDecl]
extractVars pat = 
    case pat of
    QualVar vd -> getVd vd
    ApplTerm p1 p2 _ -> 
         extractVars p1 ++ extractVars p2
    TupleTerm pats _ -> concatMap extractVars pats
    TypedTerm p _ _ _ -> extractVars p
    AsPattern v p2 _ -> getVd v ++ extractVars p2
    ResolvedMixTerm _ pats _ -> concatMap extractVars pats
    _ -> []
    where getVd vd@(VarDecl v _ _ _) = if showId v "" == "_" then [] else [vd]

-- | construct term from id
mkOpTerm :: Id -> TypeScheme -> Term
mkOpTerm i sc = QualOp Op (InstOpId i [] []) sc []

-- | bind a term
mkForall :: [GenVarDecl] -> Term -> Term
mkForall vl f = if null vl then f else QuantifiedTerm Universal vl f []

-- | construct application with curried arguments
mkApplTerm :: Term -> [Term] -> Term
mkApplTerm trm args = if null args then trm
       else mkApplTerm (ApplTerm trm (head args) []) $ tail args

-- | get the type of a constructor with given curried argument types
getConstrType :: Type -> Partiality -> [Type] -> Type
getConstrType dt p ts = (case p of 
     Total -> id 
     Partial -> addPartiality ts) $
		       foldr ( \ c r -> FunType c FunArr r [] ) dt ts

-- | make function arrow partial after some arguments
addPartiality :: [a] -> Type -> Type
addPartiality as t = case as of 
        [] -> LazyType t []
	_ : rs -> case t of 
	   FunType t1 a t2 ps -> if null rs then FunType t1 PFunArr t2 ps 
	       else FunType t1 a (addPartiality rs t2) ps
	   _ -> error "addPartiality"

-- | get the partiality from a constructor type 
-- with a given number of curried arguments
getPartiality :: [a] -> Type -> Partiality
getPartiality as t = case t of
   KindedType ty _ _ -> getPartiality as ty
   FunType _ a t2 _ -> case as of 
     [] -> Total
     [_] -> case a of 
	    PFunArr  -> Partial
	    PContFunArr -> Partial
	    _ -> Total
     _:rs -> getPartiality rs t2
   LazyType _ _ -> if null as then Partial else error "getPartiality"
   _ -> Total


-- | compute the type given by the input
typeIdToType :: Id -> [TypeArg] -> Kind -> Type
typeIdToType i nAs k = let      
    fullKind = typeArgsListToKind nAs k
    ti = TypeName i fullKind 0
    mkType ty [] = ty
    mkType ty ((TypeArg ai ak _ _): rest) =
	mkType (TypeAppl ty (TypeName ai ak 1)) rest
    in mkType ti nAs

-- | extent a kind to expect further type arguments
typeArgsListToKind :: [TypeArg] -> Kind -> Kind
typeArgsListToKind tArgs k = 
    if null tArgs then k
       else typeArgsListToKind (init tArgs) 
	    (FunKind (( \ (TypeArg _ xk _ _) -> xk) $ last tArgs) k []) 

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
    MissingKind -> nullPos
    ClassKind c _ -> posOfId c
    Downset _ t _ ps -> firstPos [t] ps 
    Intersection ks ps -> firstPos ks ps
    FunKind k1 _ ps -> firstPos [k1] ps 
    ExtKind ek _ ps -> firstPos [ek] ps

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

posOfTypeArg :: TypeArg -> Pos
posOfTypeArg (TypeArg t _ _ ps) = firstPos [t] ps

instance PosItem TypeArg where
    get_pos = Just . posOfTypeArg

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
    ExpandedType t1 t2 -> posOf [t1, t2]
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
    QualVar v -> posOfVarDecl v
    QualOp _ (InstOpId i _ ps) _ qs -> firstPos [i] (ps++qs) 
    ResolvedMixTerm i _ _ -> posOfId i
    ApplTerm t1 t2 ps -> firstPos [t1, t2] ps
    TupleTerm ts ps -> firstPos ts ps 
    TypedTerm t _ _ ps -> firstPos [t] ps 
    QuantifiedTerm _ _ t ps -> firstPos [t] ps 
    LambdaTerm _ _ t ps -> firstPos [t] ps 
    CaseTerm t _ ps -> firstPos [t] ps 
    LetTerm _ _ t ps -> firstPos [t] ps
    TermToken t -> tokPos t
    MixTypeTerm _ t ps -> firstPos [t] ps
    MixfixTerm ts -> posOf ts
    BracketTerm _ ts ps -> firstPos ts ps 
    AsPattern v _ ps -> firstPos [v] ps

-- ---------------------------------------------------------------------

posOfVarDecl :: VarDecl -> Pos
posOfVarDecl (VarDecl v _ _ ps) = firstPos [v] ps

instance PosItem VarDecl where
    get_pos = Just . posOfVarDecl
