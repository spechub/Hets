{- |
Module      :  $Header$
Description :  infer the kinds of types
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

analyse types
-}

module HasCASL.TypeAna where

import HasCASL.As
import HasCASL.FoldType
import HasCASL.AsUtils
import HasCASL.Le
import HasCASL.ClassAna
import HasCASL.TypeMixAna
import qualified Data.Map as Map
import qualified Data.Set as Set
import Common.DocUtils
import Common.Id
import Common.Result
import Common.Lib.State

import Data.Maybe
import Data.List as List

import Control.Monad

-- * infer kind

-- | extract kinds of type identifier
getIdKind :: Env -> Id -> Result ((Variance, RawKind, Set.Set Kind), Type)
getIdKind te i =
    case Map.lookup i $ localTypeVars te of
       Nothing -> case Map.lookup i $ typeMap te of
           Nothing -> mkError "unknown type" i
           Just (TypeInfo rk l _ _) ->
               return ((NonVar, rk, l), TypeName i rk 0)
       Just (TypeVarDefn v vk rk c) ->
           return ((v, rk, Set.singleton $ toKind vk), TypeName i rk c)

-- | extract kinds of co- or invariant type identifiers
getCoVarKind :: Maybe Bool -> Env -> Id
             -> Result ((RawKind, Set.Set Kind), Type)
getCoVarKind b te i = do
    ((v, rk, l), ty) <- getIdKind te i
    case (v, b) of
           (ContraVar, Just True) -> Result
               [mkDiag Hint "wrong contravariance of" i]
               $ Just ((rk, Set.empty), ty)
           (CoVar, Just False) -> Result
               [mkDiag Hint "wrong covariance of" i]
               $ Just ((rk, Set.empty), ty)
           _ -> return ((rk, l), ty)

-- | check if there is at least one solution
subKinds :: DiagKind -> ClassMap -> Type -> Set.Set Kind -> Set.Set Kind
         -> Set.Set Kind -> Result (Set.Set Kind)
subKinds dk cm ty sk ks res =
   if Set.null $ Set.filter (flip (newKind cm) ks) sk then return res
   else Result [Diag dk
        ("no kind found for '" ++ showDoc ty "'" ++
         if Set.null ks then "" else expected sk ks)
        $ getRange ty] $ if dk == Error then Nothing else Just Set.empty

-- | add an analysed type argument (warn on redeclared types)
addTypeVarDecl :: Bool -> TypeArg -> State Env ()
addTypeVarDecl warn (TypeArg i v vk rk c _ _) =
       addLocalTypeVar warn (TypeVarDefn v vk rk c) i

addLocalTypeVar :: Bool -> TypeVarDefn -> Id -> State Env ()
addLocalTypeVar warn tvd i = do
    e <- get
    let tvs = localTypeVars e
    when warn $ do
       when (Map.member i $ typeMap e)
         $ addDiags [mkDiag Warning
           "type variable shadows type constructor" i]
       when (Map.member i tvs)
         $ addDiags [mkDiag Hint "rebound type variable" i]
       when (Map.member i $ localVars e)
         $ addDiags [mkDiag Warning
           "type variable does not shadow normal variable" i]
    putLocalTypeVars $ Map.insert i tvd tvs

-- | infer all minimal kinds
inferKinds :: Maybe Bool -> Type -> Env
           -> Result ((RawKind, Set.Set Kind), Type)
inferKinds b ty te@Env{classMap = cm} = case ty of
    TypeName i _ _ -> getCoVarKind b te i
    TypeAppl t1 t2 -> do
       ((rk, ks), t3) <- inferKinds b t1 te
       case rk of
           FunKind v _ rr _ -> do
               ((_, l), t4) <- inferKinds (case v of
                            ContraVar -> Just $ maybe False not b
                            CoVar -> Just $ fromMaybe True b
                            _ -> Nothing) t2 te
               kks <- mapM (getFunKinds cm) $ Set.toList ks
               rs <- mapM ( \ fk -> case fk of
                    FunKind _ arg res _ -> subKinds Hint cm t2
                        (Set.singleton arg) l $ Set.singleton res
                    _ -> error "inferKinds: no function kind"
                  ) $ Set.toList $ keepMinKinds cm kks
               return ((rr, keepMinKinds cm rs), TypeAppl t3 t4)
           _ -> mkError "unexpected type argument" t2
    TypeAbs ta@(TypeArg _ v k r _ _ q) t ps -> do
        let newEnv = execState (addTypeVarDecl False ta) te
        ((rk, ks), nt) <- inferKinds Nothing t newEnv
        return (( FunKind v r rk q
                , keepMinKinds cm
                  [Set.map (\ j -> FunKind v (toKind k) j q) ks])
               , TypeAbs ta nt ps)
    KindedType kt kind ps -> do
        let Result ds _ = mapM (flip anaKindM cm) $ Set.toList kind
        sk <- if null ds then return kind else Result ds Nothing
        ((rk, ks), t) <- inferKinds b kt te
        l <- subKinds Hint cm kt sk ks sk
        return ((rk, l), KindedType t sk ps)
    ExpandedType t1 t2 -> do
        ((rk1, ks), t4) <- inferKinds b t2 te
        ((rk2, aks), t3) <- inferKinds b t1 te
        rk <- maybe (Result (diffKindDiag ty rk1 rk2) Nothing) return
              $ minRawKind "" rk1 rk2
        return ((rk, keepMinKinds cm [aks, ks]), ExpandedType t3 t4)
    _ -> error "inferKinds"

-- | extract the raw kind from a type term
rawKindOfType :: Type -> RawKind
rawKindOfType = foldType FoldTypeRec
  { foldTypeName = \ _ _ k _ -> k
  , foldTypeAppl = \ _ ka _ -> case ka of
        FunKind _ _ k _ -> k
        _ -> error "rawKindOfType"
  , foldExpandedType = \ _ k1 ->
        fromMaybe (error "rawKindOfType.foldExpandedType") . minRawKind "" k1
  , foldTypeAbs = \ _ (TypeArg _ v _ r _ _ _) -> FunKind v r
  , foldKindedType = \ _ k _ _ -> k
  , foldTypeToken = \ _ _ -> error "rawKindOfType.foldTypeToken"
  , foldBracketType = \ _ _ _ _ -> error "rawKindOfType.foldBracketType"
  , foldMixfixType = \ _ -> error "rawKindOfType.foldMixfixType" }

-- | subtyping relation
lesserType :: Env -> Type -> Type -> Bool
lesserType te t1 t2 = case (t1, t2) of
    (KindedType t _ _, _) -> lesserType te t t2
    (ExpandedType _ t, _) -> lesserType te t t2
    (_, KindedType t _ _) -> lesserType te t1 t
    (_, ExpandedType _ t) -> lesserType te t1 t
    (TypeName _ _ _, TypeAppl (TypeName l _ _) t) | l == lazyTypeId ->
       lesserType te t1 t
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
        || case c2 of
             (TypeName l _ _) | l == lazyTypeId -> lesserType te t1 a2
             _ -> False
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
    (t3, t4) -> t3 == t4

-- | type identifiers of a type
idsOf :: (Int -> Bool) -> Type -> Set.Set Id
idsOf b = Set.fromList . map (fst . snd) . leaves b

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
expandAux tm = replAlias $ \ i k n -> case Map.lookup i tm of
    Just TypeInfo {typeDefn = AliasTypeDefn s} ->
        ExpandedType (TypeName i k n) s
    _ -> TypeName i k n

-- | find unexpanded alias identifier
hasAlias :: TypeMap -> Type -> [Diagnosis]
hasAlias tm t =
     map ( \ i -> mkDiag Error ("unexpanded alias '" ++ showId i "' in") t)
     $ Set.toList $ Set.intersection (idsOf (const True) t) $
       Map.keysSet $ filterAliases tm

-- * resolve and analyse types

-- | resolve type and infer minimal kinds
anaTypeM :: (Maybe Kind, Type) -> Env -> Result ((RawKind, Set.Set Kind), Type)
anaTypeM (mk, parsedType) te =
    do resolvedType <- mkTypeConstrAppl te parsedType
       let tm = typeMap te
           adj = adjustPos $ getRange parsedType
           cm = classMap te
       ((rk, ks), checkedType) <- adj $ inferKinds Nothing resolvedType te
       l <- adj $ case mk of
               Nothing -> subKinds Error cm parsedType
                 (if Set.null ks then Set.singleton universe else ks) ks ks
               Just k -> subKinds Error cm parsedType (Set.singleton k) ks $
                         Set.filter (flip (lesserKind cm) k) ks
       let expandedType = expandAlias tm checkedType
       Result (hasAlias tm expandedType) $ Just ()
       return ((rk, l), expandedType)

-- | resolve the type and check if it is of the universe class
anaStarTypeM :: Type -> Env -> Result ((RawKind, Set.Set Kind), Type)
anaStarTypeM t = anaTypeM (Just universe, t)

-- * misc functions on types

-- | check if an id occurs in a type
cyclicType :: Id -> Type -> Bool
cyclicType i = Set.member i . idsOf (== 0)

-- | check for unbound (or if False for too many) type variables
unboundTypevars :: Bool -> [TypeArg] -> Type -> [Diagnosis]
unboundTypevars b args ty =
    let fvs = freeTVarIds ty
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
