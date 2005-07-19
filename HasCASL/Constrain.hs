{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
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
  getRange c = case c of 
    Kinding ty _ -> getRange ty
    Subtyping t1 t2 -> getRange t1 `appRange` getRange t2

type Constraints = Set.Set Constrain

noC :: Constraints
noC = Set.empty

joinC :: Constraints -> Constraints -> Constraints
joinC = Set.union

insertC :: Constrain -> Constraints -> Constraints
insertC c = case c of 
            Subtyping t1 t2 -> if t1 == t2 then id else Set.insert c
            Kinding _ k -> if k == star then id else Set.insert c

substC :: Subst -> Constraints -> Constraints
substC s = Set.fold (insertC . ( \ c -> case c of
    Kinding ty k -> Kinding (subst s ty) k
    Subtyping t1 t2 -> Subtyping (subst s t1) $ subst s t2)) noC

simplify :: TypeEnv -> Constraints -> ([Diagnosis], Constraints)
simplify te rs = 
    if Set.null rs then ([], noC)
    else let (r, rt) = Set.deleteFindMin rs 
             Result ds m = entail te r
             (es, cs) = simplify te rt
             in (ds ++ es, case m of
                                 Just _ -> cs
                                 Nothing -> insertC r cs)

entail :: Monad m => TypeEnv -> Constrain -> m ()
entail te p = 
    do is <- byInst te p
       mapM_ (entail te) $ Set.toList is

byInst :: Monad m => TypeEnv -> Constrain -> m Constraints
byInst te c = let cm = classMap te in case c of 
    Kinding ty k -> case ty of 
      ExpandedType _ t -> byInst te $ Kinding t k
      _ -> if k == star then return noC else case k of
           ExtKind ek _ _ -> byInst te (Kinding ty ek)
           ClassKind _ -> let (topTy, args) = getTypeAppl ty in
               case topTy of 
               TypeName i _ _ -> let Result _ mk = getIdKind te i in
                   case mk of 
                   Nothing -> fail $ "remaining variable '" 
                              ++ showPretty i "'"   
                   Just ((_, ks), _) -> do 
                       if null args then
                          if any ( \ j -> lesserKind cm j k) ks 
                             then return noC 
                             else fail $ "constrain '" ++ 
                                  showPretty c "' is unprovable"
                                  ++ "\n  known kinds are: " ++
                                  showPretty ks ""
                          else do 
                          let kas = concatMap ( \ j -> 
                                         getKindAppl cm j args) ks
                          newKs <- dom cm k kas 
                          return $ Set.fromList $ zipWith Kinding args newKs
               _ -> error "byInst: unexpected Type" 
           _ -> error "byInst: unexpected Kind" 
    Subtyping t1 t2 -> if lesserType te t1 t2 then return noC
                       else fail ("unable to prove: " ++ showPretty t1 " < " 
                                  ++ showPretty t2 "")

maxKind :: ClassMap -> Kind -> Kind -> Maybe Kind
maxKind cm k1 k2 = if lesserKind cm k1 k2 then Just k1 else 
                if lesserKind cm k2 k1 then Just k2 else Nothing

maxKinds :: ClassMap -> [Kind] -> Maybe Kind
maxKinds cm l = case l of 
    [] -> Nothing
    [k] -> Just k
    [k1, k2] -> maxKind cm k1 k2
    k1 : k2 : ks -> case maxKind cm k1 k2 of 
          Just k -> maxKinds cm (k : ks)
          Nothing -> do k <- maxKinds cm (k2 : ks)
                        maxKind cm k1 k 

maxKindss :: ClassMap -> [[Kind]] -> Maybe [Kind]
maxKindss cm l = let margs = map (maxKinds cm) $ transpose l in
   if all isJust margs then Just $ map fromJust margs
      else Nothing

dom :: Monad m => ClassMap -> Kind -> [([Kind], Kind)] -> m [Kind]
dom cm k ks = 
    let fks = filter ( \ (_, rk) -> lesserKind cm rk k ) ks 
        margs = maxKindss cm $ map fst fks
        in if null fks then fail ("class not found " ++ showPretty k "") 
           else case margs of 
              Nothing -> fail "dom: maxKind"
              Just args -> if any ((args ==) . fst) fks then return args
                           else fail "dom: not coregular"

freshTypeVarT :: Type -> State Int Type             
freshTypeVarT t = 
    do (var, c) <- freshVar $ posOfType t
       return $ TypeName var (rawKindOfType t) c

freshVarsT :: [Type] -> State Int [Type]
freshVarsT l = mapM freshTypeVarT l

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

substPairList :: Subst -> [(Type, Type)] -> [(Type, Type)]
substPairList s = map ( \ (a, b) -> (subst s a, subst s b))

-- pre: shapeMatch succeeds
shapeMgu :: TypeEnv -> [(Type, Type)] -> State (Int, Subst) [(Type, Type)]
shapeMgu te cs = 
    let (atoms, structs) = partition ( \ p -> case p of
                                       (TypeName _ _ _, TypeName _ _ _) -> True
                                       _ -> False) cs 
    in if null structs then return atoms else
    let p@(t1, t2) = head structs
        tl = tail structs 
        rest = tl ++ atoms
    in case p of 
    (ExpandedType _ t, _) -> shapeMgu te $ (t, t2) : rest
    (_, ExpandedType _ t) -> shapeMgu te $ (t1, t) : rest
    (LazyType t _, _) -> shapeMgu te $ (t, t2) : rest
    (_, LazyType t _) -> shapeMgu te $ (t1, t) : rest
    (KindedType t _ _, _) -> shapeMgu te $ (t, t2) : rest
    (_, KindedType t _ _) -> shapeMgu te $ (t1, t) : rest
    (ProductType _ _, _) -> shapeMgu te $ (convertType t1, t2) : rest
    (_, ProductType _ _) -> shapeMgu te $ (t1, convertType t2) : rest
    (FunType _ _ _ _, _) -> shapeMgu te $ (convertType t1, t2) : rest
    (_, FunType _ _ _ _) -> shapeMgu te $ (t1, convertType t2) : rest
    (TypeName _ _ v1, TypeAppl f a) -> if (v1 > 0) then do
             vf <- toPairState $ freshTypeVarT f 
             va <- toPairState $ freshTypeVarT a 
             let s = Map.singleton v1 (TypeAppl vf va)
             addSubst s
             shapeMgu te $ (vf, f) : (case rawKindOfType vf of
                 FunKind (ExtKind _ CoVar _) _ _ -> [(va, a)]
                 FunKind (ExtKind _ ContraVar _) _ _ -> [(a, va)]
                 _ -> [(a, va), (va, a)]) ++ substPairList s rest
       else error ("shapeMgu1: " ++ showPretty t1 " < " ++ showPretty t2 "") 
    (_, TypeName _ _ _) -> do ats <- shapeMgu te ((t2, t1) : map swap rest)
                              return $ map swap ats
    (TypeAppl f1 a1, TypeAppl f2 a2) -> 
         shapeMgu te $ (f1, f2) : case (rawKindOfType f1, rawKindOfType f2) of
              (FunKind (ExtKind _ CoVar _) _ _, 
               FunKind (ExtKind _ CoVar _) _ _) -> (a1, a2) : rest
              (FunKind (ExtKind _ ContraVar _) _ _, 
               FunKind (ExtKind _ ContraVar _) _ _) -> (a2, a1) : rest
              _ -> (a1, a2) : (a2, a1) : rest
    _ -> error ("shapeMgu2: " ++ showPretty t1 " < " ++ showPretty t2 "")

zipC :: Kind -> (Type, Type) -> [(Type, Type)] 
zipC k p = let q = swap p in case k of
                      ExtKind _ CoVar _ -> [p]
                      ExtKind _ ContraVar _ -> [q]
                      _ -> [p,q]

shapeUnify :: TypeEnv -> [(Type, Type)] -> State Int (Subst, [(Type, Type)])
shapeUnify te l = do 
    c <- get 
    let (r, (n, s)) = runState (shapeMgu te l) (c, eps) 
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
                         ++ showPretty c2 "'") nullRange) ws) Nothing

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

shapeMatchPairList :: TypeMap -> [(Type, Type)] -> Result Subst
shapeMatchPairList tm l = case l of
    [] -> return eps
    (t1, t2) : rt -> do 
        s1 <- shapeMatch tm t1 t2
        s2 <- shapeMatchPairList tm $ substPairList s1 rt
        return $ compSubst s1 s2

shapeRel :: TypeEnv -> Constraints 
         -> State Int (Result (Subst, Constraints, Rel.Rel Type))
shapeRel te cs = 
    let (qs, subS) = partitionC cs
        subL = toListC subS
    in case shapeMatchPairList (typeMap te) subL of
       Result ds Nothing -> return $ Result ds Nothing
       _ -> do (s1, atoms) <- shapeUnify te subL
               let r = Rel.transClosure $ Rel.fromList atoms
                   es = Map.foldWithKey ( \ t1 st l1 -> 
                             case t1 of
                             TypeName _ _ 0 -> Set.fold ( \ t2 l2 -> 
                                 case t2 of
                                 TypeName _ _ 0 -> if lesserType te t1 t2 
                                     then l2 else (t1, t2) : l2
                                 _ -> l2) l1 st
                             _ -> l1) [] $ Rel.toMap r 
               return $ if null es then 
                 case collapser r of
                   Result ds Nothing -> Result ds Nothing
                   Result _ (Just s2) -> 
                       let s = compSubst s1 s2 
                       in return (s, substC s qs, 
                                  Rel.fromList $ substPairList s2 atoms)
                 else Result (map ( \ (t1, t2) ->
                                 mkDiag Hint "rejected" $ 
                                             Subtyping t1 t2) es) Nothing

-- | compute monotonicity of a type variable
monotonic :: TypeEnv -> Int -> Type -> (Bool, Bool)
monotonic te v t = 
     case t of 
           TypeName _ _ i -> (True, i /= v)
           ExpandedType _ t2 -> monotonic te v t2
           KindedType tk _ _ -> monotonic te v tk
           LazyType tl _ -> monotonic te v tl
           _ -> let (top, args) = getTypeAppl t in case top of
                TypeName _ k _ -> 
                    let ks = snd $ getRawKindAppl k args 
                        (bs1, bs2) = unzip $ zipWith ( \ rk a ->
                             let (b1, b2) = monotonic te v a
                             in case rk of
                                       ExtKind _ CoVar _ -> (b1, b2)
                                       ExtKind _ ContraVar _ -> (b2, b1)
                                       _ -> (b1 && b2, b1 && b2)) ks args
                    in (and bs1, and bs2) 
                _ -> error "monotonic"

-- | find monotonicity based instantiation
monoSubst :: TypeEnv -> Rel.Rel Type -> Type -> Subst
monoSubst te r t = 
    let varSet = Set.fromList . leaves (> 0)
        vs = Set.toList $ Set.union (varSet t) $ Set.unions $ map varSet 
              $ Set.toList $ Rel.nodes r
        monos = filter ( \ (i, (n, rk)) -> case monotonic te i t of
                                (True, _) -> 1 == Set.size 
                                    (Rel.predecessors r $ 
                                        TypeName n rk i)
                                _ -> False) vs
        antis = filter ( \ (i, (n, rk)) -> case monotonic te i t of
                                (_, True) -> 1 == Set.size
                                     (Rel.succs r $ 
                                         TypeName n rk i)
                                _ -> False) vs
        resta = filter ( \ (i, (n, rk)) -> case monotonic te i t of
                                (True, True) -> 1 < Set.size
                                     (Rel.succs r $ 
                                         TypeName n rk i)
                                _ -> False) vs
        restb = filter ( \ (i, (n, rk)) -> case monotonic te i t of
                                (True, True) -> 1 < Set.size
                                     (Rel.predecessors r $ 
                                         TypeName n rk i)
                                _ -> False) vs
    in if null antis then 
          if null monos then 
             if null resta then
                if null restb then eps else
                    let (i, (n, rk)) = head restb
                        tn = TypeName n rk i
                        s = Rel.predecessors r tn
                        sl = Set.delete tn $ foldl1 Set.intersection 
                                      $ map (Rel.succs r)
                                      $ Set.toList s
                    in Map.singleton i $ Set.findMin $ if Set.null sl then s
                       else sl
             else   let (i, (n, rk)) = head resta
                        tn = TypeName n rk i
                        s = Rel.succs r tn
                        sl = Set.delete tn $ foldl1 Set.intersection 
                                        $ map (Rel.predecessors r)
                                        $ Set.toList s
                    in Map.singleton i $ Set.findMin $ if Set.null sl then s
                       else sl
          else Map.fromAscList $ map ( \ (i, (n, rk)) -> 
                (i, Set.findMin $ Rel.predecessors r $ 
                  TypeName n rk i)) monos
       else Map.fromAscList $ map ( \ (i, (n, rk)) -> 
                (i, Set.findMin $ Rel.succs r $ 
                  TypeName n rk i)) antis
       

monoSubsts :: TypeEnv -> Rel.Rel Type -> Type -> Subst
monoSubsts te r t = 
    let s = monoSubst te (Rel.transReduce $ Rel.irreflex r) t in
    if Map.null s then s else
       compSubst s $ 
            monoSubsts te (Rel.transClosure $ Rel.map (subst s) r) 
                           $ subst s t 

fromTypeMap :: TypeMap -> Rel.Rel Type
fromTypeMap = Map.foldWithKey (\ t ti r ->
                    foldr (Rel.insert (TypeName t (typeKind ti) 0)) r
                                  [ ty | ty@(TypeName _ _ _) <- 
                                    superTypes ti ]) Rel.empty 

