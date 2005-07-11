{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

analyse classes and types
-}

module HasCASL.TypeAna where

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Le
import HasCASL.ClassAna
import HasCASL.Unify
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Id
import Common.Result
import Common.PrettyPrint
import Data.List as List
import Data.Maybe

import Debug.Trace

-- --------------------------------------------------------------------------
-- kind analysis
-- --------------------------------------------------------------------------

type TypeEnv = Env

-- | extract kinds of type id
getIdKind :: TypeEnv -> Id -> Result (RawKind, [Kind])
getIdKind te i = 
    case Map.lookup i $ localTypeVars te of
       Nothing -> case Map.lookup i $ typeMap te of 
           Nothing -> mkError "unknown type" i
           Just (TypeInfo rk l _ _) -> return (rk, l)
       Just (TypeVarDefn rk vk _) -> return (rk, [toKind vk])

-- | extract raw kind of type id
getRawKind :: TypeEnv -> Id -> Result RawKind
getRawKind te = fmap fst . getIdKind te

-- | extract kinds of co- or invariant type id
getCoVarKind :: Maybe Bool -> TypeEnv -> Id -> Result (RawKind, [Kind])
getCoVarKind b te i = do 
    (rk, l) <- getIdKind te i
    case (rk, b) of 
           (ExtKind ek ContraVar _, Just True) -> Result
               [mkDiag Hint "wrong contravariance of" i] $ Just (ek, [])
           (ExtKind ek CoVar _, Just False) -> Result
               [mkDiag Hint "wrong covariance of" i] $ Just (ek, [])
           _ -> return (invertKindVariance False rk, 
                        map (invertKindVariance False) $ 
                            keepMinKinds (classMap te) l)

-- | create type from id 
getIdType :: Id -> TypeEnv -> Result Type
getIdType i te = do 
       rk <- getRawKind te i 
       return $ TypeName i rk $ case Map.lookup i $ localTypeVars te of
                 Just (TypeVarDefn _ _ c) -> c
                 _ -> 0

-- | construct application differently for left and right arguments 
data ApplMode = TopLevel | OnlyArg 

-- | manual mixfix resolution of parsed types
mkTypeConstrAppls :: ApplMode -> Type -> TypeEnv -> Result Type
mkTypeConstrAppls m ty te = case ty of
    TypeName _ _ _ -> return ty
    TypeAppl t1 t2 -> do 
       t3 <- mkTypeConstrAppls m t1 te
       t4 <- mkTypeConstrAppls OnlyArg t2 te
       return $ TypeAppl t3 t4
    TypeToken tt -> getIdType (simpleIdToId tt) te
    BracketType b ts ps -> do
       args <- mapM (\ trm -> mkTypeConstrAppls m trm te) ts
       case args of
                  [] -> case b of
                        Parens -> return unitType
                        _ -> let i = Id (mkBracketToken b ps) [] []
                             in getIdType i te
                  [x] -> case b of
                         Parens -> return x
                         _ -> do let [o,c] = mkBracketToken b ps 
                                     i = Id [o, Token place $ firstPos args ps
                                            , c] [] []
                                 t <- getIdType i te
                                 if isPlaceType (head ts) then return t
                                    else return $ TypeAppl t x
                  _ -> mkError "illegal type" ty
    MixfixType [] -> error "mkTypeConstrAppl (MixfixType [])"
    MixfixType (f:a) -> case (f, a) of 
      (TypeToken t, [BracketType Squares as@(_:_) ps]) -> do 
         mis <- mapM mkTypeCompId as 
         getIdType (Id [t] mis ps) te
      _ -> do newF <- mkTypeConstrAppls TopLevel f te 
              nA <- mapM ( \ t -> mkTypeConstrAppls OnlyArg t te) a
              return $ foldl1 TypeAppl $ newF : nA
    KindedType t k p -> do 
       newT <- mkTypeConstrAppls m t te
       return $ KindedType newT k p
    LazyType t p -> do
       newT <- mkTypeConstrAppls TopLevel t te
       return $ LazyType newT p 
    ProductType ts ps -> let n = length ts in 
       if all isPlaceType ts && n > 1 then 
       getIdType (productId n) te else do
       mTs <- mapM (\ t -> mkTypeConstrAppls TopLevel t te) ts
       return $ mkProductType mTs ps
    FunType t1 a t2 ps -> if isPlaceType t1 && isPlaceType t2 then
       getIdType (arrowId a) te else do
       newT1 <- mkTypeConstrAppls TopLevel t1 te
       newT2 <- mkTypeConstrAppls TopLevel t2 te
       return $ FunType newT1 a newT2 ps
    ExpandedType _ t2 -> mkTypeConstrAppls m t2 te

isPlaceType :: Type -> Bool
isPlaceType ty = case ty of 
    TypeToken t -> isPlace t
    _ -> False

mkTypeCompId :: Type -> Result Id
mkTypeCompId ty = case ty of 
    TypeToken t -> if isPlace t then mkError "unexpected place" t
                   else return $ Id [t] [] []
    MixfixType [] -> error "mkTypeCompId: MixfixType []"
    MixfixType (hd:tps) ->
         if null tps then mkTypeCompId hd
         else do 
         let (toks, comps) = break ( \ p -> 
                        case p of BracketType Squares (_:_) _ -> True
                                  _ -> False) tps
         mts <- mapM mkTypeCompToks (hd:toks)
         (mis, ps) <- if null comps then return ([], [])
                     else mkTypeCompIds $ head comps
         pls <- if null comps then return [] 
                else mapM mkTypeIdPlace $ tail comps
         return $ Id (concat mts ++ pls) mis ps 
    _ -> do ts <- mkTypeCompToks ty
            return $ Id ts [] []

mkTypeCompIds :: Type -> Result ([Id], [Pos])
mkTypeCompIds ty = case ty of
    BracketType Squares tps@(_:_) ps -> do
        mis <- mapM mkTypeCompId tps  
        return (mis, ps)
    _ -> mkError "no compound list for type id" ty

mkTypeCompToks :: Type -> Result [Token]
mkTypeCompToks ty = case ty of 
    TypeToken t -> return [t]
    BracketType bk [tp] ps -> case bk of 
        Parens -> mkError "no type id" ty
        _ -> do let [o,c] = mkBracketToken bk ps
                mts <- mkTypeCompToks tp
                return (o : mts ++ [c])
    MixfixType tps -> do
        mts <- mapM mkTypeCompToks tps
        return $ concat mts
    _ -> mkError "no type tokens" ty

mkTypeIdPlace :: Type -> Result Token
mkTypeIdPlace ty =  case ty of 
    TypeToken t -> if isPlace t then return t
                   else mkError "no place" t
    _ -> mkError "no place" ty

-- ---------------------------------------------------------------------------
-- compare types
-- ---------------------------------------------------------------------------

getKindAppl :: ClassMap -> Kind -> [a] -> [(Kind, [Kind])]
getKindAppl cm k args = if null args then [(k, [])] else
    case k of 
    FunKind k1 k2 _ -> let ks = getKindAppl cm k2 (tail args)
                       in map ( \ (rk, kargs) -> (rk, k1 : kargs)) ks
--    ExtKind ek _ _ -> getKindAppl ek args
    ClassKind ci -> case Map.lookup ci cm of 
        Just (ClassInfo _ ks) -> case ks of 
            [] -> error $ "getKindAppl1 " ++ show k
            _ -> concatMap (\ fk -> getKindAppl cm fk args) ks
        _ -> error $ "getKindAppl2 " ++ show k
    _ -> error $ "getKindAppl3 " ++ show k

getTypeAppl :: TypeEnv -> Type -> (Type, [Type])
getTypeAppl te ty = let (t, args) = getTyAppl ty in
   (t, reverse args) where
    getTyAppl typ = case typ of
        TypeName _ _ _ -> (typ, [])
        TypeAppl t1 t2 -> let (t, args) = getTyAppl t1 in (t, t2 : args)
        ExpandedType _ t -> getTyAppl t
        LazyType t _ -> getTyAppl t
        KindedType t _ _ -> getTyAppl t
        ProductType ts _ -> 
            let n = length ts
                pn = productId n
                Result _ mk = getRawKind te pn
            in case mk of
            Just rk -> (TypeName pn rk 0, ts)
            _ -> error "getTyAppl productId"
        FunType t1 a t2 _ -> 
            let i = arrowId a
                Result _ mk = getRawKind te i in
            case mk of
            Just rk -> (TypeName i rk 0, [t2, t1])
            _ -> error "getTyAppl arrowId"
        _ -> error "getTypeAppl: unresolved type"

-- | construct application left-associative
mkTypeAppl :: Type -> [Type] -> Type
mkTypeAppl = foldl ( \ c a -> TypeAppl c a)

convertType :: TypeEnv -> Type -> Type
convertType te ty = let (c, args) = getTypeAppl te ty in
    mkTypeAppl c args    

rawKindOfType :: TypeEnv -> Type -> RawKind 
rawKindOfType te ty = case ty of
    TypeName _ k _ -> k
    TypeAppl t1 _ -> case rawKindOfType te t1 of 
        FunKind _ rk _ -> rk 
        _ -> error "rawKindOfType"
    _ -> rawKindOfType te $ convertType te ty

    
lesserType :: TypeEnv -> Type -> Type -> Bool    
lesserType te t1 t2 = case (t1, t2) of
    (TypeAppl c1 a1, TypeAppl c2 a2) -> 
        let b1 = lesserType te c1 c2 
            b2 = lesserType te c2 c1
            b = b1 && b2
        in (case (rawKindOfType te c1, rawKindOfType te c2) of
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
    _ -> lesserType te (convertType te t1) $ convertType te t2
    
-- ---------------------------------------------------------------------------
-- infer kind
-- ---------------------------------------------------------------------------

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
inferKinds :: Maybe Bool -> Type -> TypeEnv -> Result (RawKind, [Kind])
inferKinds b ty te@Env{classMap = cm} = let
  resu = case ty of 
    TypeName i _ _ -> getCoVarKind b te i
    TypeAppl t1 t2 -> do 
       (rk, ks) <- inferKinds b t1 te
       case rk of 
           FunKind _ rr _ -> do 
               kks <- mapM (getFunKinds cm) ks
               rs <- mapM ( \ fk -> case fk of
                    FunKind arg res _ -> do 
                        (_, l) <- case arg of 
                            ExtKind _ ContraVar _ -> 
                                inferKinds (fmap not b) t2 te
                            ExtKind _ CoVar _ -> 
                                inferKinds b t2 te
                            _ -> inferKinds Nothing t2 te
                        let ek = case arg of 
                                 ExtKind k _ _ -> k
                                 _ -> arg
                        subKinds Hint cm t2 ek l [res]
                    _ -> error "inferKinds: no function kind"
                  ) $ keepMinKinds cm $ concat kks
               return (rr, keepMinKinds cm $ concat rs)
           _ -> mkError "unexpected type argument" t2
    KindedType t kind  _ -> do 
        let Result ds _ = anaKindM kind cm
        k <- if null ds then return kind else Result ds Nothing
        (rk, ks) <- inferKinds b t te
        l <- subKinds Hint cm t k ks [k] 
        return (rk, l)
    _ -> inferKinds b (convertType te ty) te 
  in -- trace (showPretty ty " : " ++ showPretty resu "") 
     resu

-- | resolve type and infer minimal kinds
anaTypeM :: (Maybe Kind, Type) -> TypeEnv -> Result ((RawKind, [Kind]), Type)
anaTypeM (mk, t) te = 
    do nt <- mkTypeConstrAppls TopLevel t te
       let ty = expandAlias (typeMap te) nt
           cm = classMap te
       (rk, ks) <- inferKinds (Just True) ty te
       l <- case mk of 
               Nothing -> subKinds Error cm t 
                          (if null ks then rk else head ks)
                          ks ks  
               Just k -> subKinds Error cm t k ks $ 
                         filter ( \ j -> lesserKind (classMap te) j k) ks
       return ((rk, l), ty)

-- | resolve the type and check if its a plain raw kind
anaStarTypeM :: Type -> TypeEnv -> Result ((RawKind, [Kind]), Type)
anaStarTypeM t = anaTypeM (Just star, t)

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

mkBracketToken :: BracketKind -> [Pos] -> [Token]
mkBracketToken k ps = 
       map ( \ s -> Token s ps) $ (\ (o,c) -> [o,c]) $ getBrackets k
