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
getCoVarKind :: TypeEnv -> Id -> Result (RawKind, [Kind])
getCoVarKind te i = do 
    (rk, l) <- getIdKind te i
    case rk of 
           ExtKind ek ContraVar _ -> Result
               [mkDiag Hint "wrong variance for" i] $ Just (ek, [])
           _ -> return (invertKindVariance False rk, 
                        map (invertKindVariance False) l)

-- | create type from id 
getIdType :: Id -> TypeEnv -> Result Type
getIdType i te = do 
       rk <- getRawKind te i 
       return $ TypeName i rk $ case Map.lookup i $ localTypeVars te of
                 Just (TypeVarDefn _ _ c) -> c
                 _ -> 0

-- | construct application differently for left/top and right arguments 
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

-- | infer all minimal kinds less than (or equal to) the input kind
inferSubKinds :: Kind -> Type -> TypeEnv 
              -> Result (RawKind, [Kind])
inferSubKinds k t te = do 
    (rk, ks) <- inferKinds t te 
    let rs = filter ( \ ki -> lesserKind (classMap te) ki k) ks
    return (rk, rs)

-- | check if there is at least one solution
hasSolutions :: Type -> [Kind] -> Result ()
hasSolutions ty ks = 
   if null ks then mkError "no kind found for" ty
    else return ()

{- | invert (if true) or delete (if false) variances of extended kinds 
   of type variables -}
invertLocalVariances :: Bool -> LocalTypeVars -> LocalTypeVars
invertLocalVariances b = 
    Map.map ( \ td -> case td of 
        TypeVarDefn rk (VarKind k) i -> 
              TypeVarDefn (invertKindVariance b rk) 
                              (VarKind $ invertKindVariance b k) i
        _ -> td)

-- | invert (if true) or delete variances
invertVariances :: Bool -> TypeEnv -> TypeEnv
invertVariances b te = 
    te { localTypeVars = invertLocalVariances b $ localTypeVars te }

-- | infer all minimal kinds
inferKinds :: Type -> TypeEnv -> Result (RawKind, [Kind])
inferKinds ty te@Env{classMap = cm} = let
  resu = case ty of 
    TypeName i _ _ -> getCoVarKind te i
    TypeAppl t1 t2 -> do 
       (rk, ks) <- inferKinds t1 te
       case rk of 
           FunKind _ rr _ -> do 
               kks <- mapM (getFunKinds cm) ks
               rs <- mapM ( \ fk -> case fk of
                    FunKind arg res _ -> do 
                        (_, l) <- case arg of 
                            ExtKind ek ContraVar _ -> 
                                inferSubKinds ek t2 $ 
                                           invertVariances True te 
                            ExtKind ek CoVar _ -> 
                                inferSubKinds ek t2 te
                            _ -> inferSubKinds arg t2 $ 
                                           invertVariances False te 
                        return $ if null l then [] else [res]
                    _ -> error "inferKinds: no function kind"
                  ) $ keepMinKinds cm $ concat kks
               return (rr, keepMinKinds cm $ concat rs)
           _ -> error "inferKinds: no function raw kind"
    KindedType t kind  _ -> do 
        let Result ds _ = anaKindM kind cm
        k <- if null ds then return kind else Result ds Nothing
        (rk, ks) <- inferSubKinds k t te
        return (rk, if null ks then [] else [k])
    _ -> inferKinds (convertType te ty) te 
  in -- trace (showPretty ty " : " ++ showPretty resu "") 
     resu

-- | resolve type and infer minimal kinds
anaTypeM :: (Maybe Kind, Type) -> TypeEnv -> Result ((RawKind, [Kind]), Type)
anaTypeM (mk, t) te = 
    do nt <- mkTypeConstrAppls TopLevel t te
       let ty = expandAlias (typeMap te) nt
       p <- case mk of 
           Nothing -> inferKinds ty te
           Just k -> inferSubKinds k ty te
       hasSolutions ty $ snd p
       return (p, ty)

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
        ts = zipWith ( \ (v, (i, rk)) n -> 
                       (v, TypeName i rk n)) fvs [-1, -2..]
        newTy = subst (Map.fromList ts) ty
     in if length args == length fvs then TypeScheme args newTy p
        else error "generalize"

-- | check for unbound type variables
unboundTypevars :: [TypeArg] -> Type -> [Diagnosis]
unboundTypevars args ty = 
    let restVars = map (fst . snd) (leaves (> 0) ty) List.\\ 
                   map getTypeVar args in
    if null restVars then []
       else [mkDiag Error ("unbound type variable(s)\n  "
                                  ++ showSepList ("," ++) showId 
                                  restVars " in") ty]

generalizable :: TypeScheme -> [Diagnosis]
generalizable (TypeScheme args ty _) = 
    (if null args then [] else unboundTypevars args ty)
    ++ checkUniqueTypevars args
    
-- | check uniqueness of type variables 
checkUniqueTypevars :: [TypeArg] -> [Diagnosis]
checkUniqueTypevars = checkUniqueness . map getTypeVar

mkBracketToken :: BracketKind -> [Pos] -> [Token]
mkBracketToken k ps = 
       map ( \ s -> Token s ps) $ (\ (o,c) -> [o,c]) $ getBrackets k
