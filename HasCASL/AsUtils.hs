{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005 
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

utility functions and computations of meaningful positions for
   various data types of the abstract syntax
-}

module HasCASL.AsUtils where

import HasCASL.As
import HasCASL.PrintAs() -- reexport instances
import Common.Keywords
import Common.Id
import Common.PrettyPrint
import qualified Common.Lib.Set as Set

-- | map a kind
mapKind :: (a -> b) -> AnyKind a -> AnyKind b
mapKind f k = case k of 
    ClassKind a -> ClassKind $ f a
    FunKind v a b r -> FunKind v (mapKind f a) (mapKind f b) r

-- | compute raw kind (if class ids or no higher kinds)
toRaw :: Kind -> RawKind 
toRaw = mapKind $ const ()

-- | the type universe as raw kind
rStar :: RawKind 
rStar = toRaw universe

-- | the Unit type (name)
unitType :: Type 
unitType = TypeName unitTypeId rStar 0

-- | add an additional Unit type argument to a type 
liftType :: Type -> Range -> Type
liftType t qs = FunType unitType PFunArr t qs

{- | add the Unit type as result type or convert a parsed empty tuple
   to the unit type -}
predType :: Type -> Type
predType t = case t of
                    BracketType Parens [] _ -> unitType
                    _ -> FunType t PFunArr unitType nullRange

-- | construct a product type
mkProductType :: [Type] -> Range -> Type
mkProductType ts ps = case ts of
    [] -> unitType
    [t] -> t
    _ -> ProductType ts ps

-- | convert a type with unbound variables to a scheme
simpleTypeScheme :: Type -> TypeScheme
simpleTypeScheme t = TypeScheme [] t nullRange

-- | change the type of the scheme to a 'predType'
predTypeScheme :: TypeScheme -> TypeScheme
predTypeScheme = mapTypeOfScheme predType

-- | the 'Kind' of the function type
funKind :: Kind
funKind = FunKind ContraVar universe (FunKind CoVar universe universe nullRange) nullRange

-- | construct higher order kind from arguments and result kind
mkFunKind :: [(Variance, AnyKind a)] -> AnyKind a -> AnyKind a
mkFunKind args res = foldr ( \ (v, a) k -> FunKind v a k nullRange) res args 

-- | the 'Kind' of the product type
prodKind :: Int -> Kind
prodKind n = if n > 1 then mkFunKind (replicate n (CoVar, universe)) universe
             else error "prodKind"

-- | a type name with a universe kind
toType :: Id -> Type
toType i = TypeName i rStar 0

-- | construct an infix identifier for a function arrow
arrowId :: Arrow -> Id
arrowId a = mkId $ map mkSimpleId [place, show a, place]

-- | construct a mixfix product identifier with n places 
productId :: Int -> Id
productId n = if n > 1 then
  mkId $ map mkSimpleId $ place : concat (replicate (n-1) [prodS, place])
  else error "productId"

-- | the brackets as tokens with positions
mkBracketToken :: BracketKind -> Range -> [Token]
mkBracketToken k ps = 
       map ( \ s -> Token s ps) $ (\ (o,c) -> [o,c]) $ getBrackets k

-- | construct a tuple from non-singleton lists
mkTupleTerm :: [Term] -> Range -> Term
mkTupleTerm ts ps = if isSingle ts then head ts else TupleTerm ts ps

{- | decompose an 'ApplTerm' into an application of an operation and a
     list of arguments -}
getAppl :: Term -> Maybe (Id, TypeScheme, [Term])
getAppl = thrdM reverse . getRevAppl
    where
    thrdM :: (c -> c) -> Maybe (a, b, c) -> Maybe (a, b, c)
    thrdM f = fmap ( \ (a, b, c) -> (a, b, f c))
    getRevAppl :: Term -> Maybe (Id, TypeScheme, [Term])
    getRevAppl t = case t of 
        TypedTerm trm q _ _ -> case q of 
            InType -> Nothing
            _ -> getRevAppl trm 
        QualOp _ (InstOpId i _ _) sc _ -> Just (i, sc, [])
        QualVar (VarDecl v ty _ _) -> Just (v, simpleTypeScheme ty, [])
        ApplTerm t1 t2 _ -> thrdM (t2:) $ getRevAppl t1
        _ -> Nothing

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
mkOpTerm i sc = QualOp Op (InstOpId i [] nullRange) sc nullRange

-- | bind a term
mkForall :: [GenVarDecl] -> Term -> Term
mkForall vl f = if null vl then f else QuantifiedTerm Universal vl f nullRange

-- | construct application with curried arguments
mkApplTerm :: Term -> [Term] -> Term
mkApplTerm = foldl ( \ t a -> ApplTerm t a nullRange) 

-- | make function arrow partial after some arguments
addPartiality :: [a] -> Type -> Type
addPartiality args t = case args of 
        [] -> LazyType t nullRange
        _ : rs -> case t of 
           FunType t1 a t2 ps -> if null rs then FunType t1 PFunArr t2 ps 
               else FunType t1 a (addPartiality rs t2) ps
           _ -> error "addPartiality"

-- | convert a type argument to a type
typeArgToType :: TypeArg -> Type
typeArgToType (TypeArg i _ _ rk c _ _) = TypeName i rk c

{- | convert a parameterized type identifier with a result raw kind 
     to a type application -}
patToType :: TypeId -> [TypeArg] -> RawKind -> Type
patToType i args rk = mkTypeAppl 
    (TypeName i (typeArgsListToRawKind args rk) 0)
    $ map typeArgToType args

-- | create the (raw if True) kind from type arguments
typeArgsListToRawKind :: [TypeArg] -> RawKind -> RawKind 
typeArgsListToRawKind tArgs = mkFunKind $
    map ( \ (TypeArg _ v _ rk _ _ _) -> (v, rk)) tArgs

-- | create the kind from type arguments
typeArgsListToKind :: [TypeArg] -> Kind -> Kind 
typeArgsListToKind tArgs = mkFunKind $
    map ( \ (TypeArg _ v ak _ _ _ _) -> (v, toKind ak)) tArgs

-- | get the type of a constructor with given curried argument types
getFunType :: Type -> Partiality -> [Type] -> Type
getFunType rty p ts = (case p of
     Total -> id
     Partial -> addPartiality ts) $
                       foldr ( \ c r -> FunType c FunArr r nullRange )
                             rty ts

-- | get the type of a selector given the data type as first arguemnt
getSelType :: Type -> Partiality -> Type -> Type
getSelType dt p rt = (case p of 
    Partial -> addPartiality [dt]
    Total -> id) (FunType dt FunArr rt nullRange)

-- | get the type of a constructor for printing (kinds may be wrong)
createConstrType :: Id -> [TypeArg] -> RawKind -> Partiality -> [Type] -> Type
createConstrType i is rk = 
    getFunType (patToType i is rk)

-- | get the type variable
getTypeVar :: TypeArg -> Id
getTypeVar(TypeArg v _ _ _ _ _ _) = v

-- | construct application left-associative
mkTypeAppl :: Type -> [Type] -> Type
mkTypeAppl = foldl ( \ c a -> TypeAppl c a)

-- | get the kind of an analyzed type variable
toKind :: VarKind -> Kind
toKind vk = case vk of
    VarKind k -> k
    Downset t -> case t of 
        KindedType _ k _ -> k
        _ -> error "toKind: Downset"
    MissingKind -> error "toKind: Missing"

-- | generate a comparison string 
expected :: PrettyPrint a => a -> a -> String
expected a b = 
    "\n  expected: " ++ showPretty a 
    "\n     found: " ++ showPretty b "\n" 

-- * compute better positions

posOfVars :: Vars -> Range
posOfVars vr = 
    case vr of 
    Var v -> posOfId v
    VarTuple _ ps -> ps

posOfTypeArg :: TypeArg -> Range
posOfTypeArg (TypeArg t _ _ _ _ _ ps) = firstPos [t] ps

posOfTypePattern :: TypePattern -> Range
posOfTypePattern pat = 
    case pat of
    TypePattern t _ _ -> posOfId t
    TypePatternToken t -> tokPos t
    MixfixTypePattern ts -> posOf ts
    BracketTypePattern _ ts ps -> firstPos ts ps
    TypePatternArg (TypeArg t _ _ _ _ _ _) _ -> posOfId t

posOfType :: Type -> Range
posOfType ty = 
    case ty of
    TypeName i _ _ -> posOfId i
    TypeAppl t1 t2 -> concatMapRange posOfType [t1, t2]
    ExpandedType t1 t2 -> concatMapRange posOfType [t1, t2]
    TypeToken t -> tokPos t
    BracketType _ ts ps -> concatMapRange posOfType ts `appRange` ps
    KindedType t _ ps -> posOfType t `appRange` ps
    MixfixType ts -> concatMapRange posOfType ts
    LazyType t ps -> posOfType t `appRange` ps
    ProductType ts ps -> concatMapRange posOfType ts `appRange` ps
    FunType t1 _ t2 ps -> concatMapRange posOfType [t1, t2] `appRange` ps

posOfTerm :: Term -> Range
posOfTerm trm =
    case trm of
    QualVar v -> posOfVarDecl v
    QualOp _ (InstOpId i _ ps) _ qs -> firstPos [i] (ps `appRange` qs) 
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

posOfVarDecl :: VarDecl -> Range
posOfVarDecl (VarDecl v _ _ ps) = firstPos [v] ps

instance PosItem a => PosItem [a] where
    getRange = concatMapRange getRange 

instance PosItem a => PosItem (a, b) where
    getRange (a, _) = getRange a

instance PosItem a => PosItem (Set.Set a) where
    getRange = getRange . Set.toList
