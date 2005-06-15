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
import HasCASL.ClassAna
import HasCASL.Le
import HasCASL.Unify
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Id
import Common.Result
import Common.PrettyPrint
import Data.List as List

-- --------------------------------------------------------------------------
-- kind analysis
-- --------------------------------------------------------------------------

anaKindM :: Kind -> Env -> Result Kind
anaKindM k env = 
    case k of
    MissingKind -> mkError "missing kind" k
    Downset v t _ ps -> do (rk, newT) <- anaType (Nothing, t) (typeMap env)
                           let ds = unboundTypevars [] newT
                           if null ds then 
                              return $ Downset v newT rk ps
                              else Result ds Nothing 
    ClassKind ci _ -> anaClassId ci (classMap env)
    Intersection ks ps -> do newKs <- mapM ( \ ek -> anaKindM ek env) ks
                             if null newKs then return k
                                else let ds = checkIntersection 
                                                 (rawKind $ head newKs)
                                                 $ tail newKs
                                     in if null ds then 
                                        return $ if isSingle newKs 
                                               then head newKs 
                                               else Intersection newKs ps
                                        else Result ds Nothing
    FunKind k1 k2 ps -> do k3 <- anaKindM k1 env
                           k4 <- anaKindM k2 env
                           return $ FunKind k3 k4 ps
    ExtKind ek v ps -> do nk <- anaKindM ek env
                          return $ ExtKind nk v ps

data ApplMode = OnlyArg | TopLevel 

getIdType :: Id -> TypeMap -> Result Type
getIdType i tm = do 
       k <- getIdKind tm i 
       return $ TypeName i k $ case Map.lookup i tm of
                 Just (TypeInfo _ _ _ (TypeVarDefn c)) -> c
                 _ -> 0

mkTypeConstrAppls :: ApplMode -> Type -> TypeMap -> Result Type
mkTypeConstrAppls m ty tm = case ty of
    TypeName _ _ _ -> return ty
    TypeAppl t1 t2 -> do 
       t3 <- mkTypeConstrAppls m t1 tm 
       t4 <- mkTypeConstrAppls OnlyArg t2 tm
       return $ TypeAppl t3 t4
    TypeToken tt -> getIdType (simpleIdToId tt) tm
    BracketType b ts ps -> do
       args <- mapM (\ trm -> mkTypeConstrAppls m trm tm) ts
       case args of
                  [] -> case b of
                        Parens -> return logicalType
                        _ -> let i = Id (mkBracketToken b ps) [] []
                             in getIdType i tm
                  [x] -> case b of
                         Parens -> return x
                         _ -> do let [o,c] = mkBracketToken b ps 
                                     i = Id [o, Token place $ firstPos args ps
                                            , c] [] []
                                 t <- getIdType i tm
                                 if isPlaceType (head ts) then return t
                                    else return $ TypeAppl t x
                  _ -> mkError "illegal type" ty
    MixfixType [] -> error "mkTypeConstrAppl (MixfixType [])"
    MixfixType (f:a) -> case (f, a) of 
      (TypeToken t, [BracketType Squares as@(_:_) ps]) -> do 
         mis <- mapM mkTypeCompId as 
         getIdType (Id [t] mis ps) tm
      _ -> do newF <- mkTypeConstrAppls TopLevel f tm 
              nA <- mapM ( \ t -> mkTypeConstrAppls OnlyArg t tm) a
              return $ foldl1 TypeAppl $ newF : nA
    KindedType t k p -> do 
       newT <- mkTypeConstrAppls m t tm
       return $ KindedType newT k p
    LazyType t p -> do
       newT <- mkTypeConstrAppls TopLevel t tm
       return $ LazyType newT p 
    ProductType ts ps -> if all isPlaceType ts && length ts == 2 then 
       getIdType productId tm else do
       mTs <- mapM (\ t -> mkTypeConstrAppls TopLevel t tm) ts
       return $ mkProductType mTs ps
    FunType t1 a t2 ps -> if isPlaceType t1 && isPlaceType t2 then
       getIdType (arrowId a) tm else do
       newT1 <- mkTypeConstrAppls TopLevel t1 tm
       newT2 <- mkTypeConstrAppls TopLevel t2 tm
       return $ FunType newT1 a newT2 ps
    ExpandedType _ t2 -> mkTypeConstrAppls m t2 tm

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

getKindAppl :: Kind -> [a] -> [(Kind, [Kind])]
getKindAppl k args = if null args then [(k, [])] else
    case k of 
    FunKind k1 k2 _ -> let ks = getKindAppl k2 (tail args)
                       in map ( \ (rk, kargs) -> (rk, k1 : kargs)) ks
    Intersection l _ ->
        concatMap (flip getKindAppl args) l
    ExtKind ek _ _ -> getKindAppl ek args
    ClassKind _ ck -> getKindAppl ck args
    Downset _ _ dk _ -> getKindAppl dk args
    _ -> error ("getKindAppl " ++ show k)

getTypeAppl :: TypeMap -> Type -> (Type, [Type])
getTypeAppl tm ty = let (t, args) = getTyAppl ty in
   (t, reverse args) where
    getTyAppl typ = case typ of
        TypeAppl t1 t2 -> let (t, args) = getTyAppl t1 in (t, t2 : args)
        ExpandedType _ t -> getTyAppl t
        LazyType t _ -> getTyAppl t
        KindedType t _ _ -> getTyAppl t
        ProductType ts ps -> 
            let Result _ mk = getIdKind tm productId
            in case mk of
            Just k -> 
                let rk = toIntersection (map fst $ getKindAppl k [typ,typ]) ps
                in case ts of 
                [t1,t2] -> (TypeName productId k 0, [t2, t1])
                [] -> (TypeName productId rk 0, [])
                [_] -> error "getTyAppl productType"
                t:rt -> (TypeName productId k 0, [ProductType rt ps, t])
            _ -> error "getTyAppl productId"
        FunType t1 a t2 _ -> 
            let i = arrowId a
                Result _ mk = getIdKind tm i in
            case mk of
            Just k -> (TypeName i k 0, [t2, t1])
            _ -> error "getTyAppl arrowId"
        _ -> (typ, [])

mkTypeAppl :: Type -> [Type] -> Type
mkTypeAppl t as = 
    if null as then t else mkTypeAppl (TypeAppl t $ head as) $ tail as
    
cyclicType :: Id -> Type -> Bool
cyclicType i ty = Set.member i $ idsOf (==0) ty

lesserType :: TypeMap -> Type -> Type -> Bool    
lesserType tm t1 t2 = case (t1, t2) of
    (ExpandedType _ t, _) -> lesserType tm t t2
    (_, ExpandedType _ t) -> lesserType tm t1 t
    (LazyType t _, _) -> lesserType tm t t2
    (_, LazyType t _) -> lesserType tm t1 t
    (KindedType t _ _, _) -> lesserType tm t t2
    (_, KindedType t _ _) -> lesserType tm t1 t
    (ProductType ts1 _, ProductType ts2 _) -> 
        if length ts1 == length ts2 then 
           and $ zipWith (lesserType tm) ts1 ts2
           else False
    (FunType ta1 a1 tr1 _, FunType ta2 a2 tr2 _) -> 
        (case (a1, a2) of 
        (ContFunArr, _) -> True
        (_, PFunArr) -> True
        (PContFunArr, FunArr) -> False
        (FunArr, PContFunArr) -> False
        _ -> a1 == a2) && lesserType tm tr1 tr2 && lesserType tm ta2 ta1
    _ -> let (top1, as1) = getTypeAppl tm t1
             (top2, as2) = getTypeAppl tm t2 in
            case (top1, top2) of   
            (TypeName i1 k1 _, TypeName i2 k2 _) ->
                let rk = rawKind k1
                    kindArgs k as = if null as then []
                        else case k of 
                              FunKind ka kr _ -> ka : kindArgs kr (tail as)
                              _ -> []
                    kas = kindArgs rk as1
                    ts1 = filter (not . cyclicType i1) $ superTypes 
                          $ Map.findWithDefault starTypeInfo i1 tm
                    l1 = length as1
                in if i1 == i2 then
                       if rawKind k2 == rk && l1 == length as2
                          && length kas == l1 then
                                 and $ zipWith (\ k (ta1, ta2) -> 
                                  let b1 = lesserType tm ta1 ta2
                                      b2 = lesserType tm ta2 ta1
                                  in case k of 
                                  ExtKind _ CoVar _ -> b1
                                  ExtKind _ ContraVar _ -> b2
                                  _ -> b1 && b2) kas
                                 $ zip as1 as2
                       else error ("lesserType: expected length " ++
                                   shows l1 " and kind " ++ 
                                   showPretty rk "")
                   else any (\ st -> lesserType tm (mkTypeAppl st as1) t2) ts1
            _ -> error ("lesserType: " ++ showPretty top1 " < " 
                        ++ showPretty top2 "")

-- ---------------------------------------------------------------------------
-- compare kinds
-- ---------------------------------------------------------------------------

lesserKind :: TypeMap -> Kind -> Kind -> Bool
lesserKind tm k1 k2 = 
    case (k1, k2) of 
    (MissingKind, _) -> error "lesserKind1"
    (_, MissingKind) -> error "lesserKind2"
    (_, Intersection l2@(_:_) _) -> and $ map (lesserKind tm k1) l2
    (Intersection l1@(_:_) _, _) -> or $ map (flip (lesserKind tm) k2) l1
    (ExtKind ek1 v1 _, ExtKind ek2 v2 _) -> 
        (v1 == v2) && lesserKind tm ek1 ek2
    (_, ExtKind ek2 _ _) -> lesserKind tm k1 ek2
    (ExtKind _ _ _, _) -> False
    (Intersection [] _, Intersection [] _) -> True
    (Intersection [] _, _) -> False
    (Downset _ t1 k _,  Downset _ t2 _ _) -> lesserType tm t1 t2 
                                             || lesserKind tm k k2
    (Downset _ _ k _, _) -> lesserKind tm k k2
    (ClassKind c1 k,  ClassKind c2 _) -> c1 == c2 || lesserKind tm k k2
    (ClassKind _ k, _) -> lesserKind tm k k2
    (FunKind ek rk _, FunKind ek2 rk2 _) -> 
        lesserKind tm rk rk2 && lesserKind tm ek2 ek
    (FunKind _ _ _, _) -> False


-- ---------------------------------------------------------------------------
-- infer kind
-- ---------------------------------------------------------------------------

checkMaybeKinds :: (PosItem a, PrettyPrint a) => 
              TypeMap -> a -> Maybe Kind -> Kind -> Result Kind
checkMaybeKinds tm a mk1 k2 =
    case mk1 of
           Nothing -> return k2
           Just k1 -> if lesserKind tm k1 k2 then return k1
                      else if lesserKind tm k2 k1 then return k2
                      else Result (diffKindDiag a k1 k2) Nothing

checkFunKind :: Maybe Kind -> Type -> Type -> Kind -> TypeMap -> Result Kind
checkFunKind mk t1 t2 k1 tm = 
    case k1 of 
        FunKind fk ak _ -> do 
            inferKind (Just fk) t2 tm
            checkMaybeKinds tm (TypeAppl t1 t2) mk ak 
        Intersection l@(_:_) ps -> do
            ml <- mapM ( \ k -> checkFunKind mk t1 t2 k tm) l
            return $ toIntersection ml ps
        ClassKind _ k -> checkFunKind mk t1 t2 k tm
        Downset _ _ k _ -> checkFunKind mk t1 t2 k tm
        ExtKind k _ _ -> checkFunKind mk t1 t2 k tm
        _ -> mkError "unexpected type argument" t2

inferKind :: Maybe Kind -> Type -> TypeMap -> Result Kind
inferKind mk ty tm = case ty of 
    TypeName i _ _ -> do 
       m <- getIdKind tm i
       checkMaybeKinds tm i mk m
    TypeAppl t1 t2 -> do 
       k1 <- inferKind Nothing t1 tm
       checkFunKind mk t1 t2 k1 tm
    ExpandedType _ t1 -> inferKind mk t1 tm
    FunType t1 a t2 _ -> do
       let i = arrowId a
       fk <- getIdKind tm i
       let tn = TypeName i fk 0
       inferKind mk (TypeAppl (TypeAppl tn t1) t2) tm
    ProductType ts _ -> if null ts then checkMaybeKinds tm ty mk star else
         do pk <- getIdKind tm productId
            let tn = TypeName productId pk 0
                mkAppl [t1] = t1
                mkAppl (t1:tr) = TypeAppl (TypeAppl tn t1) $ mkAppl tr
                mkAppl [] = error "inferKind: mkAppl"
            inferKind mk (mkAppl ts) tm
    LazyType t _ -> inferKind mk t tm
    KindedType t k _ -> do
       mk2 <- inferKind (Just k) t tm
       checkMaybeKinds tm t mk mk2
    _ -> mkError "unresolved type" ty

getIdKind :: TypeMap -> Id -> Result Kind
getIdKind tm i = case Map.lookup i tm of
       Nothing -> mkError "unknown type" i
       Just (TypeInfo rk l _ _) -> return $  
           if null l then rk else 
              if isSingle l then head l else Intersection l []

-- ---------------------------------------------------------------------------
anaType :: (Maybe Kind, Type) -> TypeMap -> Result (Kind, Type)
anaType (mk, t) tm = 
    do nt <- mkTypeConstrAppls TopLevel t tm
       let newTy = expandAlias tm nt
       newk <- inferKind mk newTy tm
       return (newk, newTy)

anaStarTypeR :: Type -> TypeMap -> Result (Kind, Type)
anaStarTypeR t = anaType (Just star, t)

mkGenVars :: [TypeArg] -> Type -> Type
mkGenVars fvs newTy = 
     let ts = zipWith ( \ (TypeArg i k _ _) n ->
                                   TypeName i k n) fvs [-1, -2..]
         m = Map.fromList $ zip fvs ts
     in  repl m newTy

generalize :: TypeScheme -> TypeScheme
generalize (TypeScheme args ty p) =
    let fvs = leaves (> 0) ty
        ts = zipWith ( \ (v, TypeArg i k _ _) n -> 
                       (v, TypeName i k n)) fvs [-1, -2..]
        newTy = subst (Map.fromList ts) ty
        newArgs = map snd fvs
     in if null $ newArgs List.\\ args then TypeScheme args newTy p
        else TypeScheme newArgs newTy p

-- | check for unbound type variables
unboundTypevars :: [TypeArg] -> Type -> [Diagnosis]
unboundTypevars args ty = 
    let restVars = map snd (leaves (> 0) ty) List.\\ args in
    if null restVars then []
       else [mkDiag Error ("unbound type variable(s)\n  "
                                  ++ showSepList ("," ++) showPretty 
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
