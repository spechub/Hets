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
import qualified Data.Map as Map
import qualified Data.Set as Set
import Common.DocUtils
import Common.Id
import Common.Result
import Data.List as List
import Data.Maybe
import Common.Lib.State

-- * infer kind

-- | inspect types and classes only
type TypeEnv = Env

-- | extract kinds of type identifier
getIdKind :: TypeEnv -> Id -> Result ((Variance, RawKind, [Kind]), Type)
getIdKind te i =
    case Map.lookup i $ localTypeVars te of
       Nothing -> case Map.lookup i $ typeMap te of
           Nothing -> mkError "unknown type" i
           Just (TypeInfo rk l _ _) -> return ((InVar, rk, l), TypeName i rk 0)
       Just (TypeVarDefn v vk rk c) ->
           return ((v, rk, [toKind vk]), TypeName i rk c)

-- | extract kinds of co- or invariant type identifiers
getCoVarKind :: Maybe Bool -> TypeEnv -> Id -> Result ((RawKind, [Kind]), Type)
getCoVarKind b te i = do
    ((v, rk, l), ty) <- getIdKind te i
    case (v, b) of
           (ContraVar, Just True) -> Result
               [mkDiag Hint "wrong contravariance of" i] $ Just ((rk, []), ty)
           (CoVar, Just False) -> Result
               [mkDiag Hint "wrong covariance of" i] $ Just ((rk, []), ty)
           _ -> return ((rk, keepMinKinds (classMap te) l), ty)

-- | check if there is at least one solution
subKinds :: DiagKind -> ClassMap -> Type -> Kind -> [Kind] -> [Kind]
         -> Result [Kind]
subKinds dk cm ty sk ks res =
   if any ( \ k -> lesserKind cm k sk) ks then return res
   else Result [Diag dk
        ("no kind found for '" ++ showDoc ty "'" ++
         if null ks then "" else expected sk $ head ks)
        $ getRange ty] $ Just []

-- | add an analysed type argument (warn on redeclared types)
addTypeVarDecl :: Bool -> TypeArg -> State Env ()
addTypeVarDecl warn (TypeArg i v vk rk c _ _) =
       addLocalTypeVar warn (TypeVarDefn v vk rk c) i

addLocalTypeVar :: Bool -> TypeVarDefn -> Id -> State Env ()
addLocalTypeVar warn tvd i = do
    tvs <- gets localTypeVars
    if warn then do
         tm <- gets typeMap
         case Map.lookup i tm of
             Nothing -> case Map.lookup i tvs of
                 Nothing -> return ()
                 Just _ -> addDiags [mkDiag Hint "rebound type variable" i]
             Just _ -> addDiags [mkDiag Hint
                    "type variable shadows type constructor" i]
       else return ()
    putLocalTypeVars $ Map.insert i tvd tvs

-- | infer all minimal kinds
inferKinds :: Maybe Bool -> Type -> TypeEnv -> Result ((RawKind, [Kind]), Type)
inferKinds b ty te@Env{classMap = cm} = case ty of
    TypeName i _ _ -> getCoVarKind b te i
    TypeAppl t1 t2 -> do
       ((rk, ks), t3) <- inferKinds b t1 te
       case rk of
           FunKind v _ rr _ -> do
               ((_, l), t4) <- inferKinds (case v of
                            ContraVar -> Just $ maybe False not b
                            CoVar -> Just $ maybe True id b
                            InVar -> Nothing) t2 te
               kks <- mapM (getFunKinds cm) ks
               rs <- mapM ( \ fk -> case fk of
                    FunKind _ arg res _ -> do
                        subKinds Hint cm t2 arg l [res]
                    _ -> error "inferKinds: no function kind"
                  ) $ keepMinKinds cm $ concat kks
               return ((rr, keepMinKinds cm $ concat rs), TypeAppl t3 t4)
           _ -> mkError "unexpected type argument" t2
    TypeAbs ta@(TypeArg _ v k r _ _ q) t ps -> do
        let newEnv = execState (addTypeVarDecl False ta) te
        ((rk, ks), nt) <- inferKinds Nothing t newEnv
        return ((FunKind v r rk q, map (\ j -> FunKind v (toKind k) j q) ks)
               , TypeAbs ta nt ps)
    KindedType kt kind ps -> do
        let Result ds _ = anaKindM kind cm
        k <- if null ds then return kind else Result ds Nothing
        ((rk, ks), t) <- inferKinds b kt te
        l <- subKinds Hint cm kt k ks [k]
        return ((rk, l), KindedType t k ps)
    ExpandedType t1 t2 -> do
        ((rk, ks), t4) <- inferKinds b t2 te
        ((_, aks), t3) <- inferKinds b t1 te
        return ((rk, keepMinKinds cm $ aks ++ ks), ExpandedType t3 t4)
    _ -> error "inferKinds"

-- * converting type terms

-- | throw away alias or kind information
stripType :: String -> Type -> Type
stripType msg ty = case ty of
    ExpandedType _ t -> t
    KindedType t _ _ -> t
    _ -> error $ "stripType " ++ msg

-- * subtyping relation

-- | extract the raw kind from a type term
rawKindOfType :: Type -> RawKind
rawKindOfType ty = case ty of
    TypeName _ k _ -> k
    TypeAppl t1 _ -> case rawKindOfType t1 of
        FunKind _ _ rk _ -> rk
        _ -> error "rawKindOfType"
    TypeAbs (TypeArg _ v _ r _ _ _) t ps ->
        FunKind v r (rawKindOfType t) ps
    _ -> rawKindOfType $ stripType "rawKindOfType" ty

-- | subtyping relation
lesserType :: TypeEnv -> Type -> Type -> Bool
lesserType te t1 t2 = case (t1, t2) of
    (TypeAppl c1 a1, TypeAppl c2 a2) ->
        let b1 = lesserType te a1 a2
            b2 = lesserType te a2 a1
            b = b1 && b2
        in (case (rawKindOfType c1, rawKindOfType c2) of
            (FunKind v1 _ _ _, FunKind v2 _ _ _) ->
                if v1 == v2 then case v1 of
                            CoVar -> b1
                            ContraVar -> b2
                            _ -> b
                        else b
            _ -> error "lesserType: no FunKind") && lesserType te c1 c2
    (TypeName i1 _ _, TypeName i2 _ _) | i1 == i2 -> True
    (TypeName i k _, _) -> case Map.lookup i $ localTypeVars te of
        Nothing -> case Map.lookup i $ typeMap te of
            Nothing -> False
            Just ti -> any ( \ j -> lesserType te (TypeName j k 0) t2) $
                       Set.toList $ superTypes ti
        Just (TypeVarDefn _ vk _ _) -> case vk of
            Downset t -> lesserType te t t2
            _ -> False
    (TypeAppl _ _, TypeName _ _ _) -> False
    (TypeAppl _ _, TypeAbs _ _ _) -> False
    (TypeAbs _ _ _, TypeName _ _ _) -> False
    (KindedType t _ _, _) -> lesserType te t t2
    (ExpandedType _ t, _) -> lesserType te t t2
    (_, KindedType t _ _) -> lesserType te t1 t
    (_, ExpandedType _ t) -> lesserType te t1 t
    (t3, t4) -> t3 == t4

-- * leaves of types and substitution

-- | the type name components of a type
leaves :: (Int -> Bool) -> Type -> [(Int, (Id, RawKind))]
leaves b t =
    case t of
           TypeName j k i -> if b(i)
                             then [(i, (j, k))]
                             else []
           TypeAppl t1 t2 -> leaves b t1 `List.union` leaves b t2
           TypeAbs (TypeArg i _ _ r c _ _) ty _ ->
               List.delete (c, (i, r)) $ leaves b ty
           _ -> leaves b $ stripType "leaves" t

-- | type identifiers of a type
idsOf :: (Int -> Bool) -> Type -> Set.Set TypeId
idsOf b = Set.fromList . map (fst . snd) . leaves b

-- | replace some type names with types
repl :: Map.Map Id Type -> Type -> Type
repl m = rename ( \ i k n ->
                 case Map.lookup i m of
                      Just s -> s
                      Nothing -> TypeName i k n)
-- * super type ids

-- | compute super type ids of one type id
superIds :: TypeMap -> Id -> Set.Set Id
superIds tm = supIds tm Set.empty . Set.singleton

-- | compute all super type ids for several type ids given as second argument
supIds :: TypeMap -> Set.Set Id -> Set.Set Id -> Set.Set Id
supIds tm known new =
    if Set.null new then known else
       let more = Set.unions $ map ( \ i -> superTypes
                            $ Map.findWithDefault starTypeInfo i tm)
                  $ Set.toList new
           newKnown = Set.union known new
    in supIds tm newKnown (more Set.\\ newKnown)

-- * expand alias types

-- | expand aliases in a type scheme
expand :: TypeMap -> TypeScheme -> TypeScheme
expand = mapTypeOfScheme . expandAliases

filterAliases :: TypeMap -> TypeMap
filterAliases = Map.filter ( \ ti -> case typeDefn ti of
         AliasTypeDefn _ -> True
         _ -> False)

-- | expand aliases in a type and reduce type map first
expandAlias :: TypeMap -> Type -> Type
expandAlias = expandAliases . filterAliases

-- | expand aliases in a type if type map non-null
expandAliases :: TypeMap -> Type -> Type
expandAliases tm = if Map.null tm then id else expandAux tm

-- | expand aliases in a type
expandAux :: TypeMap -> Type -> Type
expandAux tm ty = rename ( \ i k n ->
                 case Map.lookup i tm of
                      Just TypeInfo {typeDefn = AliasTypeDefn s} ->
                          ExpandedType (TypeName i k n) s
                      _ -> TypeName i k n) ty

-- | find unexpanded alias identifier
hasAlias :: TypeMap -> Type -> [Diagnosis]
hasAlias tm t =
     map ( \ i -> mkDiag Error ("unexpanded alias '" ++ showId i "' in") t)
     $ Set.toList $ Set.intersection (idsOf (const True) t) $
       Map.keysSet $ filterAliases tm

-- * resolve and analyse types

-- | resolve type and infer minimal kinds
anaTypeM :: (Maybe Kind, Type) -> TypeEnv -> Result ((RawKind, [Kind]), Type)
anaTypeM (mk, parsedType) te =
    do resolvedType <- mkTypeConstrAppl parsedType
       let tm = typeMap te
           adj = adjustPos $ getRange parsedType
           expandedType = expandAlias tm resolvedType
           cm = classMap te
       ((rk, ks), checkedType) <- adj $ inferKinds Nothing expandedType te
       l <- adj $ case mk of
               Nothing -> subKinds Error cm parsedType
                          (if null ks then universe else head ks)
                          ks ks
               Just k -> subKinds Error cm parsedType k ks $
                         filter ( \ j -> lesserKind cm j k) ks
       Result (hasAlias tm checkedType) $ Just ()
       return ((rk, l), checkedType)

-- | resolve the type and check if it is of the universe class
anaStarTypeM :: Type -> TypeEnv -> Result ((RawKind, [Kind]), Type)
anaStarTypeM t = anaTypeM (Just universe, t)

-- * misc functions on types

-- | check if an id occurs in a type
cyclicType :: Id -> Type -> Bool
cyclicType i ty = Set.member i $ idsOf (==0) ty

-- | check for unbound (or if False for too many) type variables
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

-- | check for proper generalizability (False: warn also for unused types)
generalizable :: Bool -> TypeScheme -> [Diagnosis]
generalizable b (TypeScheme args ty _) =
    unboundTypevars b args ty ++ checkUniqueTypevars args

-- | check uniqueness of type variables
checkUniqueTypevars :: [TypeArg] -> [Diagnosis]
checkUniqueTypevars = checkUniqueness . map getTypeVar
