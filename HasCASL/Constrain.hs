
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003 
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

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
import Control.Exception(assert)

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
  get_pos c = Just $ case c of 
    Kinding ty _ -> posOfType ty
    Subtyping t1 t2 -> firstPos [t1, t2] []

type Constraints = Set.Set Constrain

noC :: Constraints
noC = Set.empty

joinC :: Constraints -> Constraints -> Constraints
joinC = Set.union

substC :: Subst -> Constraints -> Constraints
substC s = Set.image (\ c -> case c of
    Kinding ty k -> Kinding (subst s ty) k
    Subtyping t1 t2 -> Subtyping (subst s t1) $ subst s t2)

simplify :: TypeMap -> Constraints -> ([Diagnosis], Constraints)
simplify tm rs = 
    if Set.isEmpty rs then ([], Set.empty)
    else let (r, rt) = Set.deleteFindMin rs 
	     Result ds m = entail tm r
             (es, cs) = simplify tm rt
             in (ds ++ es, case m of
                                 Just _ -> cs
	                         Nothing -> Set.insert r cs)
   
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
                       else if unify tm t1 t2 then return noC
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

freshTypeVarT :: TypeMap -> Type -> State Int Type             
freshTypeVarT tm t = 
    do (var, c) <- freshVar $ posOfType t
       let mp = maybeResult $ anaType (Nothing, t) tm
           k = assert (isJust mp) $ fst $ fromJust mp
       return $ TypeName var k c

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
    put (c, compSubst s o)

-- pre: shapeMatch succeeds
shapeMgu :: TypeMap -> (Type, Type) -> State (Int, Subst) ()
shapeMgu tm (t1, t2) = 
    case (t1, t2) of 
    (ExpandedType _ t, _) -> shapeMgu tm (t, t2)
    (_, ExpandedType _ t) -> shapeMgu tm (t1, t)
    (LazyType t _, _) -> shapeMgu tm (t, t2)
    (_, LazyType t _) -> shapeMgu tm (t1, t)
    (KindedType t _ _, _) -> shapeMgu tm (t, t2)
    (_, KindedType t _ _) -> shapeMgu tm (t1, t)
    (TypeName _ _ _, TypeName _ _ _) -> return ()
    (TypeName _ _ v1, _) -> assert (v1 > 0) $
         case t2 of
         ProductType ts ps -> do 
             nts <- toPairState $ freshVarsT tm ts
             addSubst $ Map.single v1 $ ProductType nts ps
             mapM_ (shapeMgu tm) $ zip nts ts
         FunType t3 ar t4 ps -> do
             v3 <- toPairState $ freshTypeVarT tm t3
             v4 <- toPairState $ freshTypeVarT tm  t4
             addSubst $ Map.single v1 $ FunType v3 ar v4 ps
             shapeMgu tm (v3, t3)
             shapeMgu tm (v4, t4)
         TypeAppl _ _ -> do 
             let (topTy, args) = getTypeAppl tm t2 
             vs <- toPairState $ freshVarsT tm args
             addSubst $ Map.single v1 $ mkTypeAppl topTy vs
             mapM_ (shapeMgu tm) $ zip vs args
         _ -> error "shapeMgu"
    (_, TypeName _ _ _) -> shapeMgu tm (t2, t1)
    (TypeAppl t3 t4, TypeAppl t5 t6) -> do
        shapeMgu tm (t3, t5)
        shapeMgu tm (t4, t6)
    (ProductType s1 _, ProductType s2 _) -> mapM_ (shapeMgu tm) $ zip s1 s2
    (FunType t3 _ t4 _, FunType t5 _ t6 _) -> do
        shapeMgu tm (t3, t5)
        shapeMgu tm (t4, t6)
    _ -> error "shapeMgu (invalid precondition)"

shapeUnify :: TypeMap -> [(Type, Type)] -> State Int Subst
shapeUnify tm l = do 
    c <- get 
    let (_, (n, t)) = runState (mapM_ (shapeMgu tm) l) (c, Map.empty) 
    put n
    return t

-- pre: same shape (after applying shapeMgu)
atomize :: TypeMap -> (Type, Type) -> [(Type, Type)]
atomize tm (t1, t2) = 
    case (t1, t2) of 
    (ExpandedType _ t, _) -> atomize tm (t, t2)
    (_, ExpandedType _ t) -> atomize tm (t1, t)
    (LazyType t _, _) -> atomize tm (t, t2)
    (_, LazyType t _) -> atomize tm (t1, t)
    (KindedType t _ _, _) -> atomize tm (t, t2)
    (_, KindedType t _ _) -> atomize tm (t1, t)
    (TypeName _ _ _, TypeName _ _ _) -> [(t1, t2)]
    _ -> 
       let (top1, as1) = getTypeAppl tm t1
           (top2, as2) = getTypeAppl tm t2
       in case (top1, top2) of 
          (TypeName _ k1 _, TypeName _ k2 _) -> 
              let r1 = rawKind k1 
                  r2 = rawKind k2 
                  (_, ks) = getRawKindAppl r1 as1 
              in assert (r1 == r2 && length as1 == length as2) $
                 (top1, top2) : (concat $ zipWith ( \ k (a1, a2) -> 
                      case k of
                      ExtKind _ CoVar _ -> [(a1, a2)]
                      ExtKind _ ContraVar _ -> [(a2,a1)]
                      _ -> [(a1, a2), (a2, a1)]) ks $ zip as1 as2)
          _ -> error "atomize"

getRawKindAppl :: Kind -> [a] -> (Kind, [Kind])
getRawKindAppl k args = if null args then (k, []) else
    case k of 
    FunKind k1 k2 _ -> let (rk, ks) = getRawKindAppl k2 (tail args)
                       in (rk, k1 : ks)
    ExtKind ek _ _ -> getRawKindAppl ek args
    _ -> error ("getRawKindAppl " ++ show k)

-- input an atomized constraint list 
collapser :: [(Type, Type)] -> Result Subst
collapser l = 
    let (_, t) = Rel.connComp $ Rel.fromList l
        t2 = Map.map (Set.partition ( \ e -> case e of 
                                      TypeName _ _ n -> n==0
                                      _ -> error "collapser")) t
        ks = Map.elems t2
        ws = filter (\ p -> Set.size (fst p) > 1) ks
    in if null ws then
       return $ foldr ( \ (cs, vs) s -> 
               if Set.isEmpty cs then 
                    extendSubst s $ Set.deleteFindMin vs
               else extendSubst s (Set.findMin cs, vs)) Map.empty ks
    else Result 
         (map ( \ (cs, _) -> 
                let (c1, rs) = Set.deleteFindMin cs
                    c2 = Set.deleteFindMin rs
                in Diag Hint ("contradicting type inclusions for '"
                         ++ showPretty c1 "' and '" 
                         ++ showPretty c2 "'") nullPos) ws) Nothing

extendSubst :: Subst -> (Type, Set.Set Type) -> Subst
extendSubst s (t, vs) = Set.fold ( \ (TypeName _ _ n) -> 
              Map.insert n t) s vs

preClose :: TypeMap -> Constraints -> State Int (Result (Subst, Constraints))
preClose tm cs = 
    let (subS, qs) = Set.partition ( \ c -> case c of
                                  Subtyping _ _ -> True
                                  Kinding _ _ -> False) cs
        subL = [ (t1, t2) | (Subtyping t1 t2) <- Set.toList subS ]
    in case shapeMatch tm (map fst subL) $ map snd subL of
       Result ds Nothing -> return $ Result ds Nothing
       _ -> do s1 <- shapeUnify tm subL
               let as = concatMap (atomize tm  . subst s1) subL
               case collapser as of
                   Result ds Nothing -> return $ Result ds Nothing
                   Result _ (Just s2) -> let s = compSubst s2 s1 in 
                     return $ return (s, Set.union (substC s qs) $ 
                       foldr ( \ (t1, t2) -> Set.insert $ Subtyping t1 t2)
                       Set.empty $ Rel.toList $ Rel.transReduce 
                            $ Rel.fromSet $ foldr ( \ p ->
                                let q@(t1, t2) = subst s2 p in
                                 if t1 == t2 then id else Set.insert q)
                             Set.empty as)
                                                                
        

