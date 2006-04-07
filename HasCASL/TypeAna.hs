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
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Id
import Common.Result
import Data.List as List
import Data.Maybe
import Control.Exception(assert)

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
       Just (TypeVarDefn v vk rk c) -> assert (c > 0) $ 
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
        ("no kind found for '" ++ showPretty ty "'" ++ 
         if null ks then "" else expected sk $ head ks)
        $ getRange ty] $ Just []

-- | infer all minimal kinds
inferKinds :: Maybe Bool -> Type -> TypeEnv -> Result ((RawKind, [Kind]), Type)
inferKinds b ty te@Env{classMap = cm} = let
  resu = case ty of 
    TypeName i _ _ -> getCoVarKind b te i
    TypeAppl t1 t2 -> do 
       ((rk, ks), t3) <- inferKinds b t1 te
       case rk of 
           FunKind v _ rr _ -> do 
               ((_, l), t4) <- case v of 
                            ContraVar -> 
                                inferKinds (fmap not b) t2 te
                            CoVar -> 
                                inferKinds b t2 te
                            InVar -> inferKinds Nothing t2 te
               kks <- mapM (getFunKinds cm) ks
               rs <- mapM ( \ fk -> case fk of
                    FunKind _ arg res _ -> do 
                        subKinds Hint cm t2 arg l [res]
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

-- | throw away alias or kind information
stripType :: Type -> Type
stripType ty = case ty of
    ExpandedType _ t -> t
    KindedType t _ _ -> t
    _ -> error "stripType"

-- * subtyping relation

-- | extract the raw kind from a type term
rawKindOfType :: Type -> RawKind 
rawKindOfType ty = case ty of
    TypeName _ k _ -> k
    TypeAppl t1 _ -> case rawKindOfType t1 of 
        FunKind _ _ rk _ -> rk 
        _ -> error "rawKindOfType"
    _ -> rawKindOfType $ stripType ty

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
    (KindedType t _ _, _) -> lesserType te t t2
    (ExpandedType _ t, _) -> lesserType te t t2
    _ -> lesserType te t1 $ stripType t2

-- * leaves of types and substitution

-- | the type name components of a type 
leaves :: (Int -> Bool) -> Type -> [(Int, (Id, RawKind))]
leaves b t = 
    case t of 
           TypeName j k i -> if b(i)
                             then [(i, (j, k))]
                             else []
           TypeAppl t1 t2 -> leaves b t1 `List.union` leaves b t2
           _ -> leaves b $ stripType t

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
                  _ -> wrap t
            _ -> wrap t
    TypeAppl t1 t2 -> 
        let (ps, ts, ta, b) = expandAliases tm t1 
            t3 = expandAlias tm t2
        in if b && length ps > length ts then 
          (ps, t3 : ts, ta, b)  -- reverse later on
          else wrap $ TypeAppl (expandAlias tm t1) t3
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
           adj = adjustPos $ getRange parsedType
           expandedType = expandAlias tm resolvedType
           cm = classMap te
       ((rk, ks), checkedType) <- adj $ inferKinds (Just True) expandedType te
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

