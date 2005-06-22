
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003 
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

constraint resolution

-}

module HasCASL.Constrain where

import HasCASL.Unify 
import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Le
import HasCASL.TypeAna
import HasCASL.ClassAna

import qualified Common.Lib.Set as Set
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Rel as Rel
import Common.Lib.State
import Common.PrettyPrint
import Common.Lib.Pretty
import Common.Keywords
import Common.Id
import Common.Result

import Data.List
import Data.Maybe

data Constrain = Kinding Type Kind
               | Subtyping Type Type 
                 deriving (Eq, Ord, Show)

instance PrettyPrint Constrain where
    printText0 ga c = case c of 
       Kinding ty k -> printText0 ga ty <+> colon 
                                      <+> printText0 ga k
       Subtyping t1 t2 -> printText0 ga t1 <+> text lessS
                                      <+> printText0 ga t2

instance PosItem Constrain where
  get_pos c = case c of 
    Kinding ty _ -> get_pos ty
    Subtyping t1 t2 -> get_pos t1 ++ get_pos t2

type Constraints = Set.Set Constrain

noC :: Constraints
noC = Set.empty

joinC :: Constraints -> Constraints -> Constraints
joinC = Set.union

insertC :: Constrain -> Constraints -> Constraints
insertC c = case c of 
            Subtyping t1 t2 -> if t1 == t2 then id else Set.insert c
            _ -> Set.insert c

substC :: Subst -> Constraints -> Constraints
substC s = Set.fold (insertC . ( \ c -> case c of
    Kinding ty k -> Kinding (subst s ty) k
    Subtyping t1 t2 -> Subtyping (subst s t1) $ subst s t2)) noC

simplify :: TypeMap -> Constraints -> ([Diagnosis], Constraints)
simplify tm rs = 
    if Set.null rs then ([], noC)
    else let (r, rt) = Set.deleteFindMin rs 
             Result ds m = entail tm r
             (es, cs) = simplify tm rt
             in (ds ++ es, case m of
                                 Just _ -> cs
                                 Nothing -> insertC r cs)

entail :: Monad m => TypeMap -> Constrain -> m ()
entail tm p = 
    do is <- byInst tm p
       mapM_ (entail tm) $ Set.toList is

byInst :: Monad m => TypeMap -> Constrain -> m Constraints
byInst tm c = case c of 
    Kinding ty k -> case ty of 
      ExpandedType _ t -> byInst tm $ Kinding t k
      _ -> case k of
           Intersection l _ -> if null l then return noC else
                          do pss <- mapM (\ ik -> byInst tm (Kinding ty ik)) l 
                             return $ Set.unions pss
           ExtKind ek _ _ -> byInst tm (Kinding ty ek)
           ClassKind _ _ -> let (topTy, args) = getTypeAppl tm ty in
               case topTy of 
               TypeName _ kind _ -> if null args then
                   if lesserKind tm kind k then return noC 
                         else fail $ expected k kind
                   else do 
                       let ks = getKindAppl kind args
                       newKs <- dom tm k ks 
                       return $ Set.fromList $ zipWith Kinding args newKs
               _ -> error "byInst: unexpected Type" 
           _ -> error "byInst: unexpected Kind" 
    Subtyping t1 t2 -> if lesserType tm t1 t2 then return noC
                       else fail ("unable to prove: " ++ showPretty t1 " < " 
                                  ++ showPretty t2 "")

maxKind :: TypeMap -> Kind -> Kind -> Maybe Kind
maxKind tm k1 k2 = if lesserKind tm k1 k2 then Just k1 else 
                if lesserKind tm k2 k1 then Just k2 else Nothing

maxKinds :: TypeMap -> [Kind] -> Maybe Kind
maxKinds tm l = case l of 
    [] -> Nothing
    [k] -> Just k
    [k1, k2] -> maxKind tm k1 k2
    k1 : k2 : ks -> case maxKind tm k1 k2 of 
          Just k -> maxKinds tm (k : ks)
          Nothing -> do k <- maxKinds tm (k2 : ks)
                        maxKind tm k1 k 

maxKindss :: TypeMap -> [[Kind]] -> Maybe [Kind]
maxKindss tm l = let margs = map (maxKinds tm) $ transpose l in
   if all isJust margs then Just $ map fromJust margs
      else Nothing

dom :: Monad m => TypeMap -> Kind -> [(Kind, [Kind])] -> m [Kind]
dom tm k ks = 
    let fks = filter ( \ (rk, _) -> lesserKind tm rk k ) ks 
        margs = maxKindss tm $ map snd fks
        in if null fks then fail ("class not found " ++ showPretty k "") 
           else case margs of 
              Nothing -> fail "dom: maxKind"
              Just args -> if any ((args ==) . snd) fks then return args
                           else fail "dom: not coregular"

-- | get kind of an analyzed type
kindOfType :: TypeMap -> Type -> Kind
kindOfType tm ty = case ty of 
    TypeName _ k _ -> k
    TypeAppl t1 t2 -> toIntersection 
                (concatMap snd $ getKindAppl (kindOfType tm t1) [t2]) 
                $ posOfType t1 ++ posOfType t2
    ExpandedType _ t1 -> kindOfType tm t1
    FunType t1 a t2 _ -> 
       let i = arrowId a
           Result _ mk = getIdKind tm i in case mk of
       Just k -> let tn = TypeName i k 0 in 
           kindOfType tm (TypeAppl (TypeAppl tn t1) t2)
       Nothing -> error "kindOfType: FunType" 
    ProductType ts ps -> let Result _ mk = getIdKind tm productId in case mk of
            Nothing -> error "kindOfType: ProductType" 
            Just k -> let 
                rk = toIntersection (map fst $ getKindAppl k [ty,ty]) ps
                tn = TypeName productId k 0 
                mkAppl [t1] = t1
                mkAppl (t1:tr) = TypeAppl (TypeAppl tn t1) $ mkAppl tr
                mkAppl [] = error "kindOfType: mkAppl"
                in if null ts then rk else kindOfType tm (mkAppl ts)
    LazyType t _ -> kindOfType tm t
    KindedType _ k _ -> k
    _ -> error "kindOfType"

freshTypeVarT :: TypeMap -> Type -> State Int Type             
freshTypeVarT tm t = 
    do (var, c) <- freshVar $ posOfType t
       return $ TypeName var (kindOfType tm t) c

freshVarsT :: TypeMap -> [Type] -> State Int [Type]
freshVarsT tm l = mapM (freshTypeVarT tm) l

toPairState :: State Int a -> State (Int, b) a 
toPairState p = 
    do (a, b) <- get
       let (r, c) = runState p a
       put (c, b)
       return r 

addSubst :: Subst -> State (Int, Subst) ()
addSubst s = do 
    (c, o) <- get
    put (c, compSubst o s)

swap :: (a, b) -> (b, a)
swap (a, b) = (b, a)

-- pre: shapeMatch succeeds
shapeMgu :: TypeMap -> [(Type, Type)] -> State (Int, Subst) [(Type, Type)]
shapeMgu tm cs = 
    let (atoms, structs) = partition ( \ p -> case p of
                                       (TypeName _ _ _, TypeName _ _ _) -> True
                                       _ -> False) cs 
    in if null structs then return atoms else
    let p@(t1, t2) = head structs
        tl = tail structs 
        rest = tl ++ atoms
    in case p of 
    (ExpandedType _ t, _) -> shapeMgu tm ((t, t2) : rest)
    (_, ExpandedType _ t) -> shapeMgu tm ((t1, t) : rest)
    (LazyType t _, _) -> shapeMgu tm ((t, t2) : rest)
    (_, LazyType t _) -> shapeMgu tm ((t1, t) : rest)
    (KindedType t _ _, _) -> shapeMgu tm ((t, t2) : rest)
    (_, KindedType t _ _) -> shapeMgu tm ((t1, t) : rest)
    (TypeName _ _ v1, _) -> if (v1 > 0) then case t2 of
         ProductType ts ps -> do
             nts <- toPairState $ freshVarsT tm ts
             let s = Map.singleton v1 $ ProductType nts ps
             addSubst s
             shapeMgu tm (zip nts ts ++ subst s rest)
         FunType t3 ar t4 ps -> do
             v3 <- toPairState $ freshTypeVarT tm t3
             v4 <- toPairState $ freshTypeVarT tm t4
             let s = Map.singleton v1 $ FunType v3 ar v4 ps
             addSubst s
             shapeMgu tm ((t3, v3) : (v4, t4) : subst s rest)
         _ -> do
             let (topTy, args) = getTypeAppl tm t2
                 (_, ks) = getRawKindAppl (rawKind $ kindOfType tm topTy) args
             vs <- toPairState $ freshVarsT tm args
             let s = Map.singleton v1 $ mkTypeAppl topTy vs
             addSubst s
             shapeMgu tm (concat (zipWith zipC ks $ zip vs args) 
                          ++ subst s rest)
       else error ("shapeMgu: " ++ showPretty t1 " < " ++ showPretty t2 "") 
    (_, TypeName _ _ _) -> do ats <- shapeMgu tm ((t2, t1) : map swap rest)
                              return $ map swap ats
    (ProductType s1 _, ProductType s2 _) -> shapeMgu tm (zip s1 s2 ++ rest)
    (FunType t3 a1 t4 _, FunType t5 a2 t6 _) ->
        let arr a = TypeName (arrowId a) funKind 0 in
        shapeMgu tm ((arr a1, arr a2) : (t5, t3) : (t4, t6) : rest)
    _ -> let (top1, as1) = getTypeAppl tm t1
             (top2, as2) = getTypeAppl tm t2
             in case (top1, top2) of 
          (TypeName _ k1 _, TypeName _ k2 _) -> 
              let r1 = rawKind k1 
                  r2 = rawKind k2 
                  (_, ks) = getRawKindAppl r1 as1 
              in if (r1 == r2 && length as1 == length as2) then
                 shapeMgu tm ((top1, top2) : 
                              concat (zipWith zipC ks $ zip as1 as2) 
                              ++ rest)
                 else error "shapeMgu"
          _ -> error ("shapeMgu: " ++ showPretty t1 " < " ++ showPretty t2 "")

zipC :: Kind -> (Type, Type) -> [(Type, Type)] 
zipC k p = let q = swap p in case k of
                      ExtKind _ CoVar _ -> [p]
                      ExtKind _ ContraVar _ -> [q]
                      _ -> [p,q]

shapeUnify :: TypeMap -> [(Type, Type)] -> State Int (Subst, [(Type, Type)])
shapeUnify tm l = do 
    c <- get 
    let (r, (n, s)) = runState (shapeMgu tm l) (c, eps) 
    put n
    return (s, r)

getRawKindAppl :: Kind -> [a] -> (Kind, [Kind])
getRawKindAppl k args = if null args then (k, []) else
    case k of 
    FunKind k1 k2 _ -> let (rk, ks) = getRawKindAppl k2 (tail args)
                       in (rk, k1 : ks)
    ExtKind ek _ _ -> getRawKindAppl ek args
    _ -> error ("getRawKindAppl " ++ show k)

-- input an atomized constraint list 
collapser :: Rel.Rel Type -> Result Subst
collapser r = 
    let t = Rel.sccOfClosure r
        ks = map (Set.partition ( \ e -> case e of 
                                      TypeName _ _ n -> n==0
                                      _ -> error "collapser")) t
        ws = filter (\ p -> Set.size (fst p) > 1) ks
    in if null ws then
       return $ foldr ( \ (cs, vs) s -> 
               if Set.null cs then 
                    extendSubst s $ Set.deleteFindMin vs
               else extendSubst s (Set.findMin cs, vs)) eps ks
    else Result 
         (map ( \ (cs, _) -> 
                let (c1, rs) = Set.deleteFindMin cs
                    c2 = Set.findMin rs
                in Diag Hint ("contradicting type inclusions for '"
                         ++ showPretty c1 "' and '" 
                         ++ showPretty c2 "'") []) ws) Nothing

extendSubst :: Subst -> (Type, Set.Set Type) -> Subst
extendSubst s (t, vs) = Set.fold ( \ (TypeName _ _ n) -> 
              Map.insert n t) s vs

-- | partition into qualification and subtyping constraints
partitionC :: Constraints -> (Constraints, Constraints)
partitionC = Set.partition ( \ c -> case c of
                             Kinding _ _ -> True
                             Subtyping _ _ -> False)

-- | convert subtypings constrains to a pair list
toListC :: Constraints -> [(Type, Type)]
toListC l = [ (t1, t2) | Subtyping t1 t2 <- Set.toList l ]

shapeRel :: TypeMap -> Constraints 
         -> State Int (Result (Subst, Constraints, Rel.Rel Type))
shapeRel tm cs = 
    let (qs, subS) = partitionC cs
        subL = toListC subS
    in case shapeMatch tm (map fst subL) $ map snd subL of
       Result ds Nothing -> return $ Result ds Nothing
       _ -> do (s1, atoms) <- shapeUnify tm subL
               let r = Rel.transClosure $ Rel.fromList atoms
                   es = Map.foldWithKey ( \ t1 st l1 -> 
                             case t1 of
                             TypeName _ _ 0 -> Set.fold ( \ t2 l2 -> 
                                 case t2 of
                                 TypeName _ _ 0 -> if lesserType tm t1 t2 
                                     then l2 else (t1, t2) : l2
                                 _ -> l2) l1 st
                             _ -> l1) [] $ Rel.toMap r 
               return $ if null es then 
                 case collapser r of
                   Result ds Nothing -> Result ds Nothing
                   Result _ (Just s2) -> 
                       let s = compSubst s1 s2 
                       in return (s, substC s qs, 
                                  Rel.fromList $ subst s2 atoms)
                 else Result (map ( \ (t1, t2) ->
                                 mkDiag Hint "rejected" $ 
                                             Subtyping t1 t2) es) Nothing

-- | compute monotonicity of a type variable
monotonic :: TypeMap -> Int -> Type -> (Bool, Bool)
monotonic tm v t = 
     case t of 
           TypeName _ _ i -> (True, i /= v)
           ExpandedType _ t2 -> monotonic tm v t2
           KindedType tk _ _ -> monotonic tm v tk
           LazyType tl _ -> monotonic tm v tl
           _ -> let (top, args) = getTypeAppl tm t in case top of
                TypeName _ k _ -> 
                    let ks = snd $ getRawKindAppl (rawKind k) args 
                        (bs1, bs2) = unzip $ zipWith ( \ rk a ->
                             let (b1, b2) = monotonic tm v a
                             in case rk of
                                       ExtKind _ CoVar _ -> (b1, b2)
                                       ExtKind _ ContraVar _ -> (b2, b1)
                                       _ -> (b1 && b2, b1 && b2)) ks args
                    in (and bs1, and bs2) 
                _ -> error "monotonic"

-- | find monotonicity based instantiation
monoSubst :: TypeMap -> Rel.Rel Type -> Type -> Subst
monoSubst tm r t = 
    let varSet = Set.fromList . leaves (> 0)
        vs = Set.toList $ Set.union (varSet t) $ Set.unions $ map varSet 
              $ Set.toList $ Rel.nodes r
        monos = filter ( \ (i, TypeArg n k _ _) -> case monotonic tm i t of
                                (True, _) -> 1 == Set.size 
                                    (Rel.predecessors r $ TypeName n k i)
                                _ -> False) vs
        antis = filter ( \ (i, TypeArg n k _ _) -> case monotonic tm i t of
                                (_, True) -> 1 == Set.size
                                     (Rel.succs r $ TypeName n k i)
                                _ -> False) vs
        resta = filter ( \ (i, TypeArg n k _ _) -> case monotonic tm i t of
                                (True, True) -> 1 < Set.size
                                     (Rel.succs r $ TypeName n k i)
                                _ -> False) vs
        restb = filter ( \ (i, TypeArg n k _ _) -> case monotonic tm i t of
                                (True, True) -> 1 < Set.size
                                     (Rel.predecessors r $ TypeName n k i)
                                _ -> False) vs
    in if null antis then 
          if null monos then 
             if null resta then
                if null restb then eps else
                    let (i, TypeArg n k _ _) = head restb
                        tn = TypeName n k i
                        s = Rel.predecessors r tn
                        sl = Set.delete tn $ foldl1 Set.intersection 
                                      $ map (Rel.succs r)
                                      $ Set.toList s
                    in Map.singleton i $ Set.findMin $ if Set.null sl then s
                       else sl
             else   let (i, TypeArg n k _ _) = head resta
                        tn = TypeName n k i
                        s = Rel.succs r tn
                        sl = Set.delete tn $ foldl1 Set.intersection 
                                        $ map (Rel.predecessors r)
                                        $ Set.toList s
                    in Map.singleton i $ Set.findMin $ if Set.null sl then s
                       else sl
          else Map.fromAscList $ map ( \ (i, TypeArg n k _ _) -> 
                (i, Set.findMin $ Rel.predecessors r $ TypeName n k i)) monos
       else Map.fromAscList $ map ( \ (i, TypeArg n k _ _) -> 
                (i, Set.findMin $ Rel.succs r $ TypeName n k i)) antis
       

monoSubsts :: TypeMap -> Rel.Rel Type -> Type -> Subst
monoSubsts tm r t = 
    let s = monoSubst tm (Rel.transReduce $ Rel.irreflex r) t in
    if Map.null s then s else
       compSubst s $ 
            monoSubsts tm (Rel.transClosure $ Rel.map (subst s) r) 
                           $ subst s t 

fromTypeMap :: TypeMap -> Rel.Rel Type
fromTypeMap = Map.foldWithKey (\ t ti r ->
                    foldr (Rel.insert (TypeName t (typeKind ti) 0)) r
                                  [ ty | ty@(TypeName _ _ _) <- 
                                    superTypes ti ]) Rel.empty 

