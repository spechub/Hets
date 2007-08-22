{- |
Module      :  $Header$
Description :  some utilities for the abstract syntax
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

utility functions and computations of meaningful positions for
   various data types of the abstract syntax
-}

module HasCASL.AsUtils where

import HasCASL.As
import HasCASL.HToken
import Common.Id
import Common.Lexer
import Common.Keywords
import Common.DocUtils
import qualified Data.Set as Set
import qualified Text.ParserCombinators.Parsec as P

-- | the string for the universe type
typeUniverseS :: String
typeUniverseS = "Type"

-- | the id of the universe type
universeId :: Id
universeId = simpleIdToId $ mkSimpleId typeUniverseS

-- | the type universe
universe :: Kind
universe = ClassKind universeId

-- | the type universe
universeWithRange :: Range -> Kind
universeWithRange r = ClassKind $ simpleIdToId $ Token typeUniverseS r

-- | the name for the Unit type
unitTypeS :: String
unitTypeS = "Unit"

-- | the identifier for the Unit type
unitTypeId :: Id
unitTypeId = simpleIdToId $ mkSimpleId unitTypeS

-- | recursively substitute type names within a type
rename :: (Id -> RawKind -> Int -> Type) -> Type -> Type
rename m t = case t of
    TypeName i k n -> m i k n
    TypeAppl t1 t2 -> TypeAppl (rename m t1) (rename m t2)
    TypeAbs v1@(TypeArg i _ _ _ c _ _) t2 ps -> TypeAbs v1 (rename
                 ( \ j k n -> if (j, n) == (i, c) then
                      TypeName j k n else  m j k n) t2) ps
    ExpandedType t1 t2 -> ExpandedType (rename m t1) (rename m t2)
    TypeToken _ -> t
    BracketType b l ps -> BracketType b (map (rename m) l) ps
    KindedType tk k ps -> KindedType (rename m tk) k ps
    MixfixType l -> MixfixType $ map (rename m) l

-- | single step beta reduce type abstractions
redStep :: Type -> Type
redStep ty = case ty of
    TypeAppl t1 t2 -> case t1 of
        TypeAbs (TypeArg i _ _ _ c _ _) b _ ->
            rename ( \ j k n -> if (j, n) == (i, c) then t2
                                else TypeName j k n) b
        ExpandedType _ t -> redStep $ TypeAppl t t2
        KindedType t _ _ -> redStep $ TypeAppl t t2
        _ -> TypeAppl (redStep t1) t2
    ExpandedType e t -> ExpandedType e $ redStep t
    KindedType t k ps -> KindedType (redStep t) k ps
    _ -> ty

-- | check if redStep will do one beta reduction step
hasRedex :: Type -> Bool
hasRedex ty = case ty of
    TypeAppl f a -> case f of
        TypeAbs _ _ _ -> True
        ExpandedType _ t -> hasRedex $ TypeAppl t a
        KindedType t _ _ -> hasRedex $ TypeAppl t a
        _ -> hasRedex f
    ExpandedType _ t -> hasRedex t
    KindedType t _ _ -> hasRedex t
    _ -> False

-- | get top-level type constructor and its arguments and beta reduce
getTypeAppl :: Type -> (Type, [Type])
getTypeAppl = getTypeApplAux True

-- | get top-level type constructor and its arguments and beta reduce if True
getTypeApplAux :: Bool -> Type -> (Type, [Type])
getTypeApplAux b ty = let (t, args) = getTyAppl ty in (t, reverse args) where
    getTyAppl typ =
      case typ of
        TypeAppl t1 t2 -> if b && hasRedex typ then getTyAppl (redStep typ)
                          else let (t, args) = getTyAppl t1 in (t, t2 : args)
        ExpandedType _ te -> let (t, args) = getTyAppl te
                             in if null args then (typ, [])
                                    else (t, args)
        KindedType t _ _ -> getTyAppl t
        _ -> (typ, [])

-- | the builtin function arrows
data Arrow = FunArr| PFunArr | ContFunArr | PContFunArr deriving (Eq, Ord)

instance Show Arrow where
    show a = case a of
        FunArr -> funS
        PFunArr -> pFun
        ContFunArr -> contFun
        PContFunArr -> pContFun

-- | construct an infix identifier for a function arrow
arrowId :: Arrow -> Id
arrowId a = mkId $ map mkSimpleId [place, show a, place]

-- | test for a function identifier
isArrow :: Id -> Bool
isArrow i = isPartialArrow i || elem i (map arrowId [FunArr, ContFunArr])

-- | test for a partial function identifier
isPartialArrow :: Id -> Bool
isPartialArrow i = elem i $ map arrowId [PFunArr, PContFunArr]

-- | construct a mixfix product identifier with n places
productId :: Int -> Range -> Id
productId n r = if n > 1 then
  mkId $ placeTok : concat (replicate (n - 1) [Token prodS r, placeTok])
  else error "productId"

-- | test for a product identifier
isProductId :: Id -> Bool
isProductId i = isProductIdWithArgs i 0

-- | test for a product identifier
isProductIdWithArgs :: Id -> Int -> Bool
isProductIdWithArgs (Id ts cs _) m = let n = length ts in
    null cs && (if m > 1 then m == div (n + 1) 2 else n > 2) && altPlaceProd ts
     where altPlaceProd l = case l of
               [] -> False
               t : r -> isPlace t && altProdPlace r
           altProdPlace l = case l of
               [] -> True
               t : r -> tokStr t == prodS && altPlaceProd r

-- | map a kind and its variance
mapKindV :: (Variance -> Variance) -> (a -> b) -> AnyKind a -> AnyKind b
mapKindV g f k = case k of
    ClassKind a -> ClassKind $ f a
    FunKind v a b r -> FunKind (g v) (mapKind f a) (mapKind f b) r

-- | map a kind and keep variance the same
mapKind :: (a -> b) -> AnyKind a -> AnyKind b
mapKind = mapKindV id

-- | compute raw kind (if class ids or no higher kinds)
toRaw :: Kind -> RawKind
toRaw = mapKind $ const ()

-- | the type universe as raw kind
rStar :: RawKind
rStar = toRaw universe

-- | the Unit type (name)
unitType :: Type
unitType = toType unitTypeId

-- | the Unit type (name)
unitTypeWithRange :: Range -> Type
unitTypeWithRange r = toType $ simpleIdToId $ Token unitTypeS r

-- | the prefix name for lazy types
lazyTypeId :: Id
lazyTypeId = mkId [mkSimpleId "?"]

-- | the kind of the lazy type constructor
coKind :: Kind
coKind = FunKind CoVar universe universe nullRange

-- | the lazy type constructor
lazyTypeConstr :: Type
lazyTypeConstr = TypeName lazyTypeId (toRaw coKind) 0

-- | make a type lazy
mkLazyType :: Type -> Type
mkLazyType t = TypeAppl lazyTypeConstr t

-- | function type
mkFunArrType :: Type -> Arrow -> Type -> Type
mkFunArrType t1 a t2 =
    mkTypeAppl (toFunType a) [t1, t2]

mkFunArrTypeWithRange :: Range -> Type -> Arrow -> Type -> Type
mkFunArrTypeWithRange r t1 a t2 =
    mkTypeAppl (TypeName (mkId [placeTok, Token (show a) r, placeTok])
                (toRaw $ funKindWithRange r) 0) [t1, t2]

-- | construct a product type
mkProductType :: [Type] -> Type
mkProductType ts = mkProductTypeWithRange ts nullRange

-- | construct a product type
mkProductTypeWithRange :: [Type] -> Range -> Type
mkProductTypeWithRange ts r = case ts of
    [] -> unitType
    [t] -> t
    _ -> let n = length ts in
         mkTypeAppl (toProdType n r) ts

-- | convert a type with unbound variables to a scheme
simpleTypeScheme :: Type -> TypeScheme
simpleTypeScheme t = TypeScheme [] t nullRange

{- | add the unit type as result type or convert a parsed empty tuple
   to the unit type -}
predType :: Range -> Type -> Type
predType r t = case t of
    BracketType Parens [] _ -> unitTypeWithRange r
    _ -> mkFunArrTypeWithRange r t PFunArr $ unitTypeWithRange r

-- | change the type of the scheme to a 'predType'
predTypeScheme :: Range -> TypeScheme -> TypeScheme
predTypeScheme r = mapTypeOfScheme $ predType r

-- | check for and remove predicate arrow
unPredType :: Type -> (Bool, Type)
unPredType t = case getTypeAppl t of
    (TypeName at _ 0, [ty, TypeName ut (ClassKind _) 0]) |
         ut == unitTypeId && at == arrowId PFunArr -> (True, ty)
    (TypeName ut (ClassKind _) 0, []) | ut == unitTypeId ->
         (True, BracketType Parens [] nullRange) -- for printing only
    _ -> (False, t)

-- | test if type is a predicate type
isPredType :: Type -> Bool
isPredType = fst . unPredType

-- |  remove predicate arrow in a type scheme
unPredTypeScheme :: TypeScheme -> TypeScheme
unPredTypeScheme = mapTypeOfScheme (snd . unPredType)

funKindWithRange :: Range -> Kind
funKindWithRange r = FunKind ContraVar (universeWithRange r)
          (FunKind CoVar (universeWithRange r) (universeWithRange r) r) r

-- | the kind of the function type
funKind :: Kind
funKind = funKindWithRange nullRange

-- | construct higher order kind from arguments and result kind
mkFunKind :: Range -> [(Variance, AnyKind a)] -> AnyKind a -> AnyKind a
mkFunKind r args res = foldr ( \ (v, a) k -> FunKind v a k r) res args

-- | the 'Kind' of the product type
prodKind :: Int -> Range -> Kind
prodKind n r =
    if n > 1 then mkFunKind r (replicate n (CoVar, universe)) universe
    else error "prodKind"

-- | a type name with a universe kind
toType :: Id -> Type
toType i = TypeName i rStar 0

-- | the type name for a function arrow
toFunType :: Arrow -> Type
toFunType a = TypeName (arrowId a) (toRaw funKind) 0

-- | the type name for a function arrow
toProdType :: Int -> Range -> Type
toProdType n r = TypeName (productId n r) (toRaw $ prodKind n r) 0

-- | the brackets as tokens with positions
mkBracketToken :: BracketKind -> Range -> [Token]
mkBracketToken k ps =
    map ( \ s -> Token s ps) $ (\ (o,c) -> [o,c]) $ getBrackets k

-- | construct a tuple from non-singleton lists
mkTupleTerm :: [Term] -> Range -> Term
mkTupleTerm ts ps = if isSingle ts then head ts else TupleTerm ts ps

-- | try to extract tuple arguments
getTupleArgs :: Term -> Maybe [Term]
getTupleArgs t = case t of
    TypedTerm trm qt _ _ -> case qt of
      InType -> Nothing
      _ -> getTupleArgs trm
    TupleTerm ts _ -> Just ts
    _ -> Nothing

{- | decompose an 'ApplTerm' into an application of an operation and a
     list of arguments -}
getAppl :: Term -> Maybe (Id, TypeScheme, [Term])
getAppl = thrdM reverse . getRevAppl where
    thrdM :: (c -> c) -> Maybe (a, b, c) -> Maybe (a, b, c)
    thrdM f = fmap ( \ (a, b, c) -> (a, b, f c))
    getRevAppl :: Term -> Maybe (Id, TypeScheme, [Term])
    getRevAppl t = case t of
        TypedTerm trm q _ _ -> case q of
            InType -> Nothing
            _ -> getRevAppl trm
        QualOp _ (PolyId i _ _) sc _ _ -> Just (i, sc, [])
        QualVar (VarDecl v ty _ _) -> Just (v, simpleTypeScheme ty, [])
        ApplTerm t1 t2 _ -> thrdM (t2:) $ getRevAppl t1
        _ -> Nothing

-- | extract bindings from an analysed pattern
extractVars :: Term -> [VarDecl]
extractVars pat = case pat of
    QualVar vd -> getVd vd
    ApplTerm p1 p2 _ ->
         extractVars p1 ++ extractVars p2
    TupleTerm pats _ -> concatMap extractVars pats
    TypedTerm p _ _ _ -> extractVars p
    AsPattern v p2 _ -> getVd v ++ extractVars p2
    ResolvedMixTerm _ _ pats _ -> concatMap extractVars pats
    _ -> []
    where getVd vd@(VarDecl v _ _ _) = if showId v "" == "_" then [] else [vd]

-- | construct term from id
mkOpTerm :: Id -> TypeScheme -> Term
mkOpTerm i sc = QualOp Op (PolyId i [] nullRange) sc [] nullRange

-- | bind a term
mkForall :: [GenVarDecl] -> Term -> Term
mkForall vl f = if null vl then f else QuantifiedTerm Universal vl f nullRange

-- | construct application with curried arguments
mkApplTerm :: Term -> [Term] -> Term
mkApplTerm = foldl ( \ t a -> ApplTerm t a nullRange)

-- | make function arrow partial after some arguments
addPartiality :: [a] -> Type -> Type
addPartiality args t = case args of
    [] -> mkLazyType t
    _ : rs -> case getTypeAppl t of
        (TypeName a _ _, [t1, t2]) | a == arrowId FunArr ->
            if null rs then mkFunArrType t1 PFunArr t2
            else mkFunArrType t1 FunArr $ addPartiality rs t2
        _ -> error "addPartiality"

-- | convert a type argument to a type
typeArgToType :: TypeArg -> Type
typeArgToType (TypeArg i _ _ rk c _ _) = TypeName i rk c

{- | convert a parameterized type identifier with a result raw kind
     to a type application -}
patToType :: Id -> [TypeArg] -> RawKind -> Type
patToType i args rk =
    mkTypeAppl (TypeName i (typeArgsListToRawKind args rk) 0)
    $ map typeArgToType args

-- | create the (raw if True) kind from type arguments
typeArgsListToRawKind :: [TypeArg] -> RawKind -> RawKind
typeArgsListToRawKind tArgs = mkFunKind (posOf tArgs) $
    map ( \ (TypeArg _ v _ rk _ _ _) -> (v, rk)) tArgs

-- | create the kind from type arguments
typeArgsListToKind :: [TypeArg] -> Kind -> Kind
typeArgsListToKind tArgs = mkFunKind (posOf tArgs) $
    map ( \ (TypeArg _ v ak _ _ _ _) -> (v, toKind ak)) tArgs

-- | get the type of a constructor with given curried argument types
getFunType :: Type -> Partiality -> [Type] -> Type
getFunType rty p ts = (case p of
    Total -> id
    Partial -> addPartiality ts)
    $ foldr ( \ c r -> mkFunArrType c FunArr r) rty ts

-- | get the type of a selector given the data type as first arguemnt
getSelType :: Type -> Partiality -> Type -> Type
getSelType dt p rt = (case p of
    Partial -> addPartiality [dt]
    Total -> id) $ mkFunArrType dt FunArr rt

-- | make type argument invariant
inVarTypeArg :: TypeArg -> TypeArg
inVarTypeArg (TypeArg i _ vk rk c o p) = TypeArg i InVar vk rk c o p

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

-- | try to reparse the pretty printed input as an identifier
reparseAsId :: Pretty a => a -> Maybe Id
reparseAsId t = case P.parse (opId << P.eof) "" $ showDoc t "" of
               Right x -> Just x
               _ -> Nothing

-- | generate a comparison string
expected :: Pretty a => a -> a -> String
expected a b =
    "\n  expected: " ++ showDoc a
    "\n     found: " ++ showDoc b "\n"

instance PosItem a => PosItem [a] where
    getRange = concatMapRange getRange

instance PosItem a => PosItem (a, b) where
    getRange (a, _) = getRange a

instance PosItem a => PosItem (Set.Set a) where
    getRange = getRange . Set.toList

