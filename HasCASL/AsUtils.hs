{- |
Module      :  $Header$
Description :  some utilities for the abstract syntax
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

utility functions and computations of meaningful positions for
   various data types of the abstract syntax
-}

module HasCASL.AsUtils where

import HasCASL.As
import HasCASL.FoldType
import HasCASL.HToken

import Common.DocUtils
import Common.Id
import Common.Keywords
import Common.Parsec

import qualified Data.Set as Set
import qualified Text.ParserCombinators.Parsec as P

-- | the string for the universe type
typeUniverseS :: String
typeUniverseS = "Type"

-- | the id of the universe type
universeId :: Id
universeId = stringToId typeUniverseS

-- | the type universe
universe :: Kind
universe = ClassKind universeId

-- | the type universe
universeWithRange :: Range -> Kind
universeWithRange = ClassKind . simpleIdToId . Token typeUniverseS

-- | the name for the Unit type
unitTypeS :: String
unitTypeS = "Unit"

-- | the identifier for the Unit type
unitTypeId :: Id
unitTypeId = stringToId unitTypeS

-- | single step beta reduce type abstractions
redStep :: Type -> Maybe Type
redStep ty = case ty of
    TypeAppl t1 t2 -> case t1 of
        TypeAbs (TypeArg _ _ _ _ c _ _) b _ -> return $
            foldType mapTypeRec
            { foldTypeName = \ t _ _ n -> if n == c then t2 else t
            , foldTypeAbs = \ t v1@(TypeArg _ _ _ _ n _ _) tb p ->
                if n == c then t else TypeAbs v1 tb p } b
        ExpandedType _ t -> redStep $ TypeAppl t t2
        KindedType t _ _ -> redStep $ TypeAppl t t2
        _ -> do
          r1 <- redStep t1
          redStep $ TypeAppl r1 t2
    ExpandedType e t -> fmap (ExpandedType e) $ redStep t
    KindedType t k ps -> do
      r <- redStep t
      return $ KindedType r k ps
    _ -> fail "unreducible"

strippedType :: Type -> Type
strippedType = foldType mapTypeRec
    { foldTypeAppl = \ trm f a -> let t = TypeAppl f a in
        case redStep trm of
          Nothing -> case f of
            TypeName i _ 0
              | i == lazyTypeId -> a
              | isArrow i -> TypeAppl (toFunType PFunArr) a
            _ -> t
          Just r -> strippedType r
    , foldTypeName = \ _ i k v -> TypeName (if v >= 0 then i else typeId) k v
    , foldKindedType = \ _ t _ _ -> t
    , foldExpandedType = \ _ _ t -> t }

eqStrippedType :: Type -> Type -> Bool
eqStrippedType t1 t2 = strippedType t1 == strippedType t2

-- | get top-level type constructor and its arguments and beta reduce
getTypeAppl :: Type -> (Type, [Type])
getTypeAppl = getTypeApplAux True

-- | get top-level type constructor and its arguments and beta reduce if True
getTypeApplAux :: Bool -> Type -> (Type, [Type])
getTypeApplAux b ty = let (t, args) = getTyAppl ty in (t, reverse args) where
    getTyAppl typ =
      case typ of
        TypeAppl t1 t2 -> case redStep typ of
           Just r | b -> getTyAppl r
           _ -> let (t, args) = getTyAppl t1 in (t, t2 : args)
        ExpandedType _ te -> let (t, args) = getTyAppl te in case t of
           TypeName {} -> (t, args)
           _ -> if null args then (typ, []) else (t, args)
        KindedType t _ _ -> getTyAppl t
        _ -> (typ, [])

-- | the builtin function arrows
data Arrow = FunArr | PFunArr | ContFunArr | PContFunArr deriving (Eq, Ord)

instance Show Arrow where
    show a = case a of
        FunArr -> funS
        PFunArr -> pFun
        ContFunArr -> contFun
        PContFunArr -> pContFun

arrowIdRange :: Range -> Arrow -> Id
arrowIdRange r a = mkId $ map (`Token` r) [place, show a, place]

-- | construct an infix identifier for a function arrow
arrowId :: Arrow -> Id
arrowId = arrowIdRange nullRange

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
    FunKind v a b r -> FunKind (g v) (mapKindV g f a) (mapKindV g f b) r

-- | map a kind and keep variance the same
mapKind :: (a -> b) -> AnyKind a -> AnyKind b
mapKind = mapKindV id

-- | ignore variances of raw kinds
nonVarRawKind :: RawKind -> RawKind
nonVarRawKind = mapKindV (const NonVar) id

-- | compute raw kind (if class ids or no higher kinds)
toRaw :: Kind -> RawKind
toRaw = mapKind $ const ()

-- | the type universe as raw kind
rStar :: RawKind
rStar = ClassKind ()

-- | the Unit type (name)
unitType :: Type
unitType = toType unitTypeId

-- | the Unit type (name)
unitTypeWithRange :: Range -> Type
unitTypeWithRange = toType . simpleIdToId . Token unitTypeS

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
mkLazyType = TypeAppl lazyTypeConstr

-- | function type
mkFunArrType :: Type -> Arrow -> Type -> Type
mkFunArrType = mkFunArrTypeWithRange nullRange

mkFunArrTypeWithRange :: Range -> Type -> Arrow -> Type -> Type
mkFunArrTypeWithRange r t1 a t2 = mkTypeAppl (toFunTypeRange r a) [t1, t2]

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
    BracketType Parens [] _ -> mkLazyType $ unitTypeWithRange r
    _ -> mkFunArrTypeWithRange r t PFunArr $ unitTypeWithRange r

-- | change the type of the scheme to a 'predType'
predTypeScheme :: Range -> TypeScheme -> TypeScheme
predTypeScheme = mapTypeOfScheme . predType

-- | check for and remove predicate arrow
unPredType :: Type -> (Bool, Type)
unPredType t = case getTypeAppl t of
    (TypeName at _ 0, [ty, TypeName ut (ClassKind _) 0])
        | ut == unitTypeId && at == arrowId PFunArr -> (True, ty)
    (TypeName lt _ 0, [TypeName ut (ClassKind _) 0])
        | ut == unitTypeId && lt == lazyTypeId ->
         (True, BracketType Parens [] nullRange) -- for printing only
    _ -> (False, t)

-- | test if type is a predicate type
isPredType :: Type -> Bool
isPredType = fst . unPredType

-- |  remove predicate arrow in a type scheme
unPredTypeScheme :: TypeScheme -> TypeScheme
unPredTypeScheme = mapTypeOfScheme (snd . unPredType)

funKindWithRange3 :: Range -> Kind -> Kind -> Kind -> Kind
funKindWithRange3 r a b c = FunKind ContraVar a (FunKind CoVar b c r) r

funKind3 :: Kind -> Kind -> Kind -> Kind
funKind3 = funKindWithRange3 nullRange

funKindWithRange :: Range -> Kind
funKindWithRange r = let c = universeWithRange r in funKindWithRange3 r c c c

-- | the kind of the function type
funKind :: Kind
funKind = funKindWithRange nullRange

-- | construct higher order kind from arguments and result kind
mkFunKind :: Range -> [(Variance, AnyKind a)] -> AnyKind a -> AnyKind a
mkFunKind r args res = foldr ( \ (v, a) k -> FunKind v a k r) res args

-- | the 'Kind' of the product type
prodKind1 :: Int -> Range -> Kind -> Kind
prodKind1 n r c =
    if n > 1 then mkFunKind r (replicate n (CoVar, c)) c
    else error "prodKind"

prodKind :: Int -> Range -> Kind
prodKind n r = prodKind1 n r universe

-- | a type name with a universe kind
toType :: Id -> Type
toType i = TypeName i rStar 0

toFunTypeRange :: Range -> Arrow -> Type
toFunTypeRange r a = TypeName (arrowIdRange r a) (toRaw $ funKindWithRange r) 0

-- | the type name for a function arrow
toFunType :: Arrow -> Type
toFunType = toFunTypeRange nullRange

-- | the type name for a function arrow
toProdType :: Int -> Range -> Type
toProdType n r = TypeName (productId n r) (toRaw $ prodKind n r) 0

-- | the brackets as tokens with positions
mkBracketToken :: BracketKind -> Range -> [Token]
mkBracketToken k ps =
    map (flip Token ps) $ (\ (o, c) -> [o, c]) $ getBrackets k

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
        QualOp _ (PolyId i _ _) sc _ _ _ -> Just (i, sc, [])
        QualVar (VarDecl v ty _ _) -> Just (v, simpleTypeScheme ty, [])
        ApplTerm t1 t2 _ -> thrdM (t2 :) $ getRevAppl t1
        _ -> Nothing

-- | split the list of generic variables into values and type variables
splitVars :: [GenVarDecl] -> ([VarDecl], [TypeArg])
splitVars l = let f x (vs, tvs) =
                      case x of
                        GenVarDecl vd -> (vd : vs, tvs)
                        GenTypeVarDecl tv -> (vs, tv : tvs)
              in foldr f ([], []) l


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
mkOpTerm i sc = QualOp Op (PolyId i [] nullRange) sc [] Infer nullRange

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
            if null rs then case getTypeAppl t2 of
                (TypeName l _ _, [t3]) | l == lazyTypeId
                   -> mkFunArrType t1 PFunArr t3
                _ -> mkFunArrType t1 PFunArr t2
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
typeArgsListToRawKind tArgs = mkFunKind (getRange tArgs) $
    map (\ (TypeArg _ v _ rk _ _ _) -> (v, rk)) tArgs

-- | create the kind from type arguments
typeArgsListToKind :: [TypeArg] -> Kind -> Kind
typeArgsListToKind tArgs = mkFunKind (getRange tArgs) $
    map ( \ (TypeArg _ v ak _ _ _ _) -> (v, toKind ak)) tArgs

-- | get the type of a constructor with given curried argument types
getFunType :: Type -> Partiality -> [Type] -> Type
getFunType rty p ts = (case p of
    Total -> id
    Partial -> addPartiality ts)
    $ foldr (`mkFunArrType` FunArr) rty ts

-- | get the type of a selector given the data type as first arguemnt
getSelType :: Type -> Partiality -> Type -> Type
getSelType dt p = (case p of
    Partial -> addPartiality [dt]
    Total -> id) . mkFunArrType dt FunArr

-- | make type argument non-variant
nonVarTypeArg :: TypeArg -> TypeArg
nonVarTypeArg (TypeArg i _ vk rk c o p) = TypeArg i NonVar vk rk c o p

-- | get the type variable
getTypeVar :: TypeArg -> Id
getTypeVar (TypeArg v _ _ _ _ _ _) = v

-- | construct application left-associative
mkTypeAppl :: Type -> [Type] -> Type
mkTypeAppl = foldl TypeAppl

-- | get the kind of an analyzed type variable
toKind :: VarKind -> Kind
toKind vk = case vk of
    VarKind k -> k
    Downset t -> case t of
        KindedType _ k _ | Set.size k == 1 -> Set.findMin k
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
