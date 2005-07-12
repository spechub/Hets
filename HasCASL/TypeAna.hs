{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

analyse types
-}

module HasCASL.TypeAna where

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Le
import HasCASL.ClassAna
import HasCASL.TypeMixAna
import HasCASL.Unify
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Id
import Common.Result
import Common.PrettyPrint
import Data.List as List
import Data.Maybe
import Control.Exception(assert)

-- * infer kind

-- | inspect types and classes only 
type TypeEnv = Env

-- | extract kinds of type identifier
getIdKind :: TypeEnv -> Id -> Result ((RawKind, [Kind]), Type)
getIdKind te i = 
    case Map.lookup i $ localTypeVars te of
       Nothing -> case Map.lookup i $ typeMap te of 
           Nothing -> mkError "unknown type" i
           Just (TypeInfo rk l _ _) -> return ((rk, l), TypeName i rk 0)
       Just (TypeVarDefn rk vk c) -> assert (c > 0) $ 
           return ((rk, [toKind vk]), TypeName i rk c)

-- | extract kinds of co- or invariant type identifiers
getCoVarKind :: Maybe Bool -> TypeEnv -> Id -> Result ((RawKind, [Kind]), Type)
getCoVarKind b te i = do 
    ((rk, l), ty) <- getIdKind te i
    case (rk, b) of 
           (ExtKind ek ContraVar _, Just True) -> Result
               [mkDiag Hint "wrong contravariance of" i] $ Just ((ek, []), ty)
           (ExtKind ek CoVar _, Just False) -> Result
               [mkDiag Hint "wrong covariance of" i] $ Just ((ek, []), ty)
           _ -> return ((invertKindVariance False rk, 
                        map (invertKindVariance False) $ 
                            keepMinKinds (classMap te) l), ty)

-- | check if there is at least one solution
subKinds :: DiagKind -> ClassMap -> Type -> Kind -> [Kind] -> [Kind] 
         -> Result [Kind]
subKinds dk cm ty sk ks res = 
   if any ( \ k -> lesserKind cm k sk) ks then return res
   else Result [Diag dk
        ("no kind found for '" ++ showPretty ty "'" ++ 
         if null ks then "" else expected sk $ head ks)
        $ posOfType ty] $ Just []

-- | infer all minimal kinds
inferKinds :: Maybe Bool -> Type -> TypeEnv -> Result ((RawKind, [Kind]), Type)
inferKinds b ty te@Env{classMap = cm} = let
  resu = case ty of 
    TypeName i _ _ -> getCoVarKind b te i
    TypeAppl t1 t2 -> do 
       ((rk, ks), t3) <- inferKinds b t1 te
       case rk of 
           FunKind rarg rr _ -> do 
               ((_, l), t4) <- case rarg of 
                            ExtKind _ ContraVar _ -> 
                                inferKinds (fmap not b) t2 te
                            ExtKind _ CoVar _ -> 
                                inferKinds b t2 te
                            _ -> inferKinds Nothing t2 te
               kks <- mapM (getFunKinds cm) ks
               rs <- mapM ( \ fk -> case fk of
                    FunKind arg res _ -> do 
                        let ek = case arg of 
                                 ExtKind k _ _ -> k
                                 _ -> arg
                        subKinds Hint cm t2 ek l [res]
                    _ -> error "inferKinds: no function kind"
                  ) $ keepMinKinds cm $ concat kks
               return ((rr, keepMinKinds cm $ concat rs), TypeAppl t3 t4)
           _ -> mkError "unexpected type argument" t2
    KindedType kt kind ps -> do 
        let Result ds _ = anaKindM kind cm
        k <- if null ds then return kind else Result ds Nothing
        ((rk, ks), t) <- inferKinds b kt te
        l <- subKinds Hint cm kt k ks [k] 
        return ((rk, l), KindedType t k ps)
    ProductType ts ps -> do 
        l <- mapM ( \ t -> inferKinds b t te) ts
        let res@(Result _ mk) = inferKinds b (convertType ty) te 
        case mk of 
            Just (kp, _) -> return (kp, ProductType (map snd l) ps)
            Nothing -> res
    LazyType t ps -> do
        (kp, nt) <- inferKinds b t te
        return (kp,  LazyType nt ps)
    FunType t1 a t2 ps -> do 
        (_, t3) <- inferKinds (fmap not b) t1 te
        (_, t4) <- inferKinds b t2 te
        let res@(Result _ mk) = inferKinds b (convertType ty) te
        case mk of 
            Just (kp, _) -> return (kp, FunType t3 a t4 ps)
            Nothing -> res
    ExpandedType t1 t2 -> do 
        let Result _ mk = inferKinds b t1 te
        (kp, t4) <- inferKinds b t2 te
        return (kp, case mk of 
                Just (_, t3) -> ExpandedType t3 t4
                Nothing -> t4)
    _ -> error "inferKinds"
  in -- trace (showPretty ty " : " ++ showPretty resu "") 
     resu

-- * converting type terms

-- | change lazy, product and fun types to type constructor name with arguments
getTypeAppl :: Type -> (Type, [Type])
getTypeAppl ty = let (t, args) = getTyAppl ty in
   (t, reverse args) where
    getTyAppl typ = case typ of
        TypeName _ _ _ -> (typ, [])
        TypeAppl t1 t2 -> let (t, args) = getTyAppl t1 in (t, t2 : args)
        ExpandedType _ t -> getTyAppl t
        LazyType t ps -> getTyAppl $ liftType t ps
        KindedType t _ _ -> getTyAppl t
        ProductType ts _ ->  let n = length ts in 
           (TypeName (productId n) (prodKind n) 0, ts)
        FunType t1 a t2 _ -> (TypeName (arrowId a) funKind 0, [t2, t1])
        _ -> error "getTypeAppl: unresolved type"

-- | construct application left-associative
mkTypeAppl :: Type -> [Type] -> Type
mkTypeAppl = foldl ( \ c a -> TypeAppl c a)

-- | change lazy, product and fun types to uniform applications
convertType :: Type -> Type
convertType ty = let (c, args) = getTypeAppl ty in mkTypeAppl c args    

-- * subtyping relation

-- | extract the raw kind from a type term
rawKindOfType :: Type -> RawKind 
rawKindOfType ty = case ty of
    TypeName _ k _ -> k
    TypeAppl t1 _ -> case rawKindOfType t1 of 
        FunKind _ rk _ -> rk 
        _ -> error "rawKindOfType"
    _ -> rawKindOfType $ convertType ty

-- | subtyping relation    
lesserType :: TypeEnv -> Type -> Type -> Bool    
lesserType te t1 t2 = case (t1, t2) of
    (TypeAppl c1 a1, TypeAppl c2 a2) -> 
        let b1 = lesserType te c1 c2 
            b2 = lesserType te c2 c1
            b = b1 && b2
        in (case (rawKindOfType c1, rawKindOfType c2) of
            (FunKind ak1 _ _, FunKind ak2 _ _) -> 
                case (ak1, ak2) of 
                    (ExtKind _ v1 _, ExtKind _ v2 _) -> 
                        if v1 == v2 then case v1 of 
                            CoVar -> b1
                            ContraVar -> b2 
                        else b
                    _ -> b
            _ -> error "lesserType: no FunKind") && lesserType te a1 a2
    (TypeName i1 _ _, TypeName i2 _ _) | i1 == i2 -> True
    (TypeName i _ _, _) -> case Map.lookup i $ localTypeVars te of 
        Nothing -> case Map.lookup i $ typeMap te of
            Nothing -> error "lesserType: lookup"
            Just ti -> any ( \ t -> lesserType te t t2) $ superTypes ti
        Just (TypeVarDefn _ vk _) -> case vk of 
            Downset t -> lesserType te t t2
            _ -> False
    (TypeAppl _ _, TypeName _ _ _) -> False
    _ -> lesserType te (convertType t1) $ convertType t2
    
-- * expand alias types

-- | replace some type names with types
repl :: Map.Map Id Type -> Type -> Type
repl m = rename ( \ i k n -> 
                 case Map.lookup i m of
                      Just s -> s 
                      Nothing -> TypeName i k n)

-- | expand aliases in a type scheme
expand :: TypeMap -> TypeScheme -> TypeScheme
expand = mapTypeOfScheme . expandAlias  

-- | expand aliases in a type 
expandAlias :: TypeMap -> Type -> Type
expandAlias tm t = 
    let (ps, ts, ta, b) = expandAliases tm t in
       if b && length ps == length ts then
          ExpandedType t $ repl (Map.fromList (zip 
                             (map getTypeVar ps) $ reverse ts)) ta
          else ta

{- | Collect formal and actual parameters of the first argument of a
type application. -}
expandAliases :: TypeMap -> Type -> ([TypeArg], [Type], Type, Bool)
expandAliases tm t = case t of 
    TypeName i _ _ -> case Map.lookup i tm of 
            Just ti -> case typeDefn ti of
                  AliasTypeDefn (TypeScheme l ty _) ->
                     (l, [], ty, True)
                  Supertype _ (TypeScheme l ty _) _ ->
                     case ty of 
                     TypeName _ _ _ -> wrap t
                     _ -> (l, [], ty, True)
                  _ -> wrap t
            _ -> wrap t
    TypeAppl t1 t2 -> 
        let (ps, ts, ta, b) = expandAliases tm t1 
            t3 = expandAlias tm t2
        in if b then 
          (ps, t3 : ts, ta, b)  -- reverse later on
          else wrap $ TypeAppl t1 t3
    FunType t1 a t2 ps -> 
        wrap $ FunType (expandAlias tm t1) a (expandAlias tm t2) ps
    ProductType ts ps -> wrap $ ProductType (map (expandAlias tm) ts) ps
    LazyType ty ps -> wrap $ LazyType (expandAlias tm ty) ps
    ExpandedType t1 t2 -> wrap $ ExpandedType t1 $ expandAlias tm t2
    KindedType ty k ps -> wrap $ KindedType (expandAlias tm ty) k ps
    _ -> wrap t
    where wrap ty = ([], [], ty, False)

-- | find unexpanded alias identifier
hasAlias :: TypeMap -> Type -> [Diagnosis]
hasAlias tm t = 
     map ( \ i -> mkDiag Error ("unexpanded alias '" ++ showId i "' in") t)
     $ filter ( \ i -> case Map.lookup i tm of
                         Just ti -> case typeDefn ti of
                              AliasTypeDefn _ -> True
                              _ -> False
                         _ -> False) $ Set.toList $ idsOf (const True) t

-- * resolve and analyse types

-- | resolve type and infer minimal kinds
anaTypeM :: (Maybe Kind, Type) -> TypeEnv -> Result ((RawKind, [Kind]), Type)
anaTypeM (mk, parsedType) te = 
    do resolvedType <- mkTypeConstrAppl parsedType
       let tm = typeMap te
           expandedType = expandAlias tm resolvedType
           cm = classMap te
       ((rk, ks), checkedType) <- inferKinds (Just True) expandedType te
       l <- case mk of 
               Nothing -> subKinds Error cm parsedType 
                          (if null ks then rk else head ks)
                          ks ks  
               Just k -> subKinds Error cm parsedType k ks $ 
                         filter ( \ j -> lesserKind cm j k) ks
       Result (hasAlias tm checkedType) $ Just ()
       return ((rk, l), checkedType)

-- | resolve the type and check if it is of the universe class
anaStarTypeM :: Type -> TypeEnv -> Result ((RawKind, [Kind]), Type)
anaStarTypeM t = anaTypeM (Just star, t)

-- * misc functions on types

-- | check if an id occurs in a type
cyclicType :: Id -> Type -> Bool
cyclicType i ty = Set.member i $ idsOf (==0) ty

-- | mark bound variables in type 
mkGenVars :: [TypeArg] -> Type -> Type
mkGenVars fvs newTy = 
     let ts = zipWith ( \ (TypeArg i vk _ _) n ->
                                   TypeName i (toKind vk) n) fvs [-1, -2..]
         m = Map.fromList $ zip (map getTypeVar fvs) ts
     in  repl m newTy

generalize :: TypeScheme -> TypeScheme
generalize (TypeScheme args ty p) =
    let fvs = leaves (> 0) ty
        svs = sortBy comp fvs
        comp a b = compare (fst a) $ fst b
        ts = zipWith ( \ (v, (i, rk)) n -> 
                       (v, TypeName i rk n)) svs [-1, -2..]
        newTy = subst (Map.fromList ts) ty
     in if map getTypeVar args == map (fst . snd) svs 
        then TypeScheme args newTy p
        else error "generalize"

-- | check for unbound (or too many) type variables
unboundTypevars :: Bool -> [TypeArg] -> Type -> [Diagnosis]
unboundTypevars b args ty = 
    let fvs = map (fst . snd) (leaves (> 0) ty)
        argIds = map getTypeVar args 
        restVars1 = fvs List.\\ argIds
        restVars2 = argIds List.\\ fvs
    in (if null restVars1 then []
       else [mkDiag Error ("unbound type variable(s)\n  "
                                  ++ showSepList ("," ++) showId 
                                  restVars1 " in") ty])
       ++ if b || null restVars2 then [] else
            [mkDiag Warning ("ignoring unused variable(s)\n  "
                                  ++ showSepList ("," ++) showId 
                                  restVars2 " in") ty]

generalizable :: TypeScheme -> [Diagnosis]
generalizable (TypeScheme args ty _) = 
    (if null args then [] else unboundTypevars False args ty)
    ++ checkUniqueTypevars args
    
-- | check uniqueness of type variables 
checkUniqueTypevars :: [TypeArg] -> [Diagnosis]
checkUniqueTypevars = checkUniqueness . map getTypeVar

