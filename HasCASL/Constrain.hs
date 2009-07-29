{- |
Module      :  $Header$
Description :  resolve type constraints
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

constraint resolution
-}

module HasCASL.Constrain
    ( Constraints
    , Constrain(..)
    , noC
    , substC
    , joinC
    , insertC
    , shapeRel
    , monoSubsts
    , fromTypeVars
    , fromTypeMap
    , entail
    , simplify
    ) where

import HasCASL.Unify
import HasCASL.As
import HasCASL.FoldType
import HasCASL.AsUtils
import HasCASL.Le
import HasCASL.PrintLe ()
import HasCASL.TypeAna
import HasCASL.ClassAna
import HasCASL.VarDecl

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Common.Lib.Rel as Rel
import Common.Lib.State
import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Result
import Common.Utils

import Control.Exception (assert)

import Data.List
import Data.Maybe

instance Pretty Constrain where
    pretty c = case c of
       Kinding ty k -> pretty $ KindedType ty (Set.singleton k) nullRange
       Subtyping t1 t2 -> fsep [pretty t1, less <+> pretty t2]

instance GetRange Constrain where
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
            Kinding _ k -> if k == universe then id else Set.insert c

substC :: Subst -> Constraints -> Constraints
substC s = Set.fold (insertC . ( \ c -> case c of
    Kinding ty k -> Kinding (subst s ty) k
    Subtyping t1 t2 -> Subtyping (subst s t1) $ subst s t2)) noC

simplify :: Env -> Constraints -> ([Diagnosis], Constraints)
simplify te rs =
    if Set.null rs then ([], noC)
    else let (r, rt) = Set.deleteFindMin rs
             Result ds m = entail te r
             (es, cs) = simplify te rt
             in (ds ++ es, case m of
                                 Just _ -> cs
                                 Nothing -> insertC r cs)

entail :: Monad m => Env -> Constrain -> m ()
entail te c = let cm = classMap te in case c of
    Kinding ty k -> if k == universe then
                        assert (rawKindOfType ty == ClassKind ())
                    $ return () else
      let Result _ds mk = inferKinds Nothing ty te in
                   case mk of
                   Nothing -> fail $ "constrain '" ++
                                  showDoc c "' is unprovable"
                   Just ((_, ks), _) -> if newKind cm k ks then
                       fail $ "constrain '" ++
                           showDoc c "' is unprovable" ++
                              if Set.null ks then "" else
                                  "\n  known kinds are: " ++ showDoc ks ""
                       else return ()
    Subtyping t1 t2 -> if lesserType te t1 t2 then return ()
                       else fail ("unable to prove: " ++ showDoc t1 " < "
                                  ++ showDoc t2 "")

freshLeaves :: Type -> State Int Type
freshLeaves ty = case ty of
    TypeName i k _ -> do
      (var, c) <- freshVar i
      return $ TypeName var k c
    TypeAppl tl@(TypeName l _ _) t | l == lazyTypeId -> do
      nt <- freshLeaves t
      return $ TypeAppl tl nt
    TypeAppl f a -> case redStep ty of
        Just r -> freshLeaves r
        Nothing -> do
          nf <- freshLeaves f
          na <- freshLeaves a
          return $ TypeAppl nf na
    KindedType t k p -> do
      nt <- freshLeaves t
      return $ KindedType nt k p
    ExpandedType _ t | noAbs t -> freshLeaves t
    ExpandedType e t -> do
      ne <- freshLeaves e
      nt <- freshLeaves t
      return $ ExpandedType ne nt
    TypeAbs _ _ _ -> return ty
    _ -> error "freshLeaves"

substPairList :: Subst -> [(Type, Type)] -> [(Type, Type)]
substPairList s = map ( \ (a, b) -> (subst s a, subst s b))

isAtomic :: (Type, Type) -> Bool
isAtomic p = case p of
    (TypeName _ _ _, TypeName _ _ _) -> True
    (TypeName _ _ _, TypeAppl (TypeName l _ _) (TypeName _ _ _)) ->
      l == lazyTypeId
    _ -> False

partEqShapes :: [(Type, Type)] -> [(Type, Type)]
partEqShapes = filter ( \ p -> case p of
    (TypeName _ _ n1, TypeName _ _ n2) -> n1 /= n2
    (TypeName _ _ n1, TypeAppl (TypeName l _ _) (TypeName _ _ n2)) ->
        l == lazyTypeId && n1 /= n2
    _ -> True)

-- pre: shapeMatchPairList succeeds
shapeMgu :: [(Type, Type)] -> [(Type, Type)] -> State Int (Result Subst)
shapeMgu knownAtoms cs = let (atoms, sts) = span isAtomic cs in
  case sts of
  [] -> return $ return eps
  p@(t1, t2) : tl -> let
   newKnowns = knownAtoms ++ partEqShapes atoms
   rest = newKnowns ++ tl
   in case p of
    (ExpandedType _ t, _) | noAbs t -> shapeMgu newKnowns $ (t, t2) : tl
    (_, ExpandedType _ t) | noAbs t -> shapeMgu newKnowns $ (t1, t) : tl
    (KindedType t _ _, _) -> shapeMgu newKnowns $ (t, t2) : tl
    (_, KindedType t _ _) -> shapeMgu newKnowns $ (t1, t) : tl
    (TypeName _ _ v1, _) | v1 > 0 -> do
             vt <- freshLeaves t2
             let s = Map.singleton v1 vt
             Result ds mr <- shapeMgu [] $ (vt, t2) : substPairList s rest
             case mr of
               Just r -> return $ return $ compSubst s r
               Nothing -> return $ Result ds Nothing
    (TypeAppl (TypeName l _ _) t, TypeName _ _ _) | l == lazyTypeId ->
        shapeMgu newKnowns $ (t, t2) : tl
    (_, TypeName _ _ v2) | v2 > 0 -> do
             vt <- freshLeaves t1
             let s = Map.singleton v2 vt
             Result ds mr <- shapeMgu [] $ (t1, vt) : substPairList s rest
             case mr of
               Just r -> return $ return $ compSubst s r
               Nothing -> return $ Result ds Nothing
    (TypeAppl f1 a1, TypeAppl f2 a2) -> case (f1, f2) of
      (TypeName l1 _ _, TypeName l2 _ _)
        | l1 == lazyTypeId && l2 == lazyTypeId ->
            shapeMgu newKnowns $ (a1, a2) : tl
      (_, TypeName l _ _) | l == lazyTypeId ->
        shapeMgu newKnowns $ (t1, a2) : tl
      (TypeName l _ _, _) | l == lazyTypeId ->
        shapeMgu newKnowns $ (a1, t2) : tl
      _ -> case redStep t1 of
        Just r1 -> shapeMgu newKnowns $ (r1, t2) : tl
        Nothing -> case redStep t2 of
          Just r2 -> shapeMgu newKnowns $ (t1, r2) : tl
          Nothing -> shapeMgu newKnowns $ (f1, f2) :
            case (rawKindOfType f1, rawKindOfType f2) of
                     (FunKind CoVar _ _ _,
                       FunKind CoVar _ _ _) -> (a1, a2) : tl
                     (FunKind ContraVar _ _ _,
                       FunKind ContraVar _ _ _) -> (a2, a1) : tl
                     _ -> (a1, a2) : (a2, a1) : tl
    _ -> shapeMgu newKnowns tl -- ignore non-matching pairs

inclusions :: [(Type, Type)] -> [(Type, Type)]
inclusions cs = let (atoms, sts) = partition isAtomic cs in
    case sts of
      [] -> atoms
      p@(t1, t2) : tl -> atoms ++ case p of
        (ExpandedType _ t, _) | noAbs t -> inclusions $ (t, t2) : tl
        (_, ExpandedType _ t) | noAbs t -> inclusions $ (t1, t) : tl
        (KindedType t _ _, _) -> inclusions $ (t, t2) : tl
        (_, KindedType t _ _) -> inclusions $ (t1, t) : tl
        (TypeAppl (TypeName l _ _) t, TypeName _ _ _) | l == lazyTypeId ->
            inclusions $ (t, t2) : tl
        _ -> case redStep t1 of
             Nothing -> case redStep t2 of
               Nothing -> case p of
                 (TypeAppl f1 a1, TypeAppl f2 a2) -> case (f1, f2) of
                   (TypeName l1 _ _, TypeName l2 _ _)
                     | l1 == lazyTypeId && l2 == lazyTypeId ->
                       inclusions $ (a1, a2) : tl
                   (_, TypeName l _ _)
                     | l == lazyTypeId ->
                       inclusions $ (t1, a2) : tl
                   (TypeName l _ _, _)
                     | l == lazyTypeId ->
                       inclusions $ (a1, t2) : tl
                   _ -> inclusions $
                    (f1, f2) : case (rawKindOfType f1, rawKindOfType f2) of
                     (FunKind CoVar _ _ _,
                       FunKind CoVar _ _ _) -> (a1, a2) : tl
                     (FunKind ContraVar _ _ _,
                       FunKind ContraVar _ _ _) -> (a2, a1) : tl
                     _ -> (a1, a2) : (a2, a1) : tl
                 _ -> p : inclusions tl
               Just r2 -> inclusions $ (t1, r2) : tl
             Just r1 -> inclusions $ (r1, t2) : tl

shapeUnify :: [(Type, Type)] -> State Int (Result (Subst, [(Type, Type)]))
shapeUnify l = do
    Result ds ms <- shapeMgu [] l
    case ms of
      Just s -> return $ Result ds $ Just (s, inclusions $ substPairList s l)
      Nothing -> return $ Result ds Nothing

-- input an atomized constraint list
collapser :: Rel.Rel Type -> Result Subst
collapser r =
    let t = Rel.sccOfClosure r
        ks = map (Set.partition ( \ e -> case e of
               TypeName _ _ n -> n == 0
               TypeAppl (TypeName l _ _) (TypeName _ _ n) ->
                   n == 0 && l == lazyTypeId
               _ -> error "collapser")) t
        ws = filter (hasMany . fst) ks
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
                         ++ showDoc c1 "' and '"
                         ++ showDoc c2 "'") nullRange) ws) Nothing

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

shapeRel :: Env -> Constraints
         -> State Int (Result (Subst, Constraints, Rel.Rel Type))
shapeRel te cs =
    let (qs, subS) = partitionC cs
        subL = toListC subS
    in case shapeMatchPairList (typeMap te) subL of
       Result ds Nothing -> return $ Result ds Nothing
       _ -> do
         Result rs msa <- shapeUnify subL
         case msa of
           Just (s1, atoms0) ->
               let atoms = filter isAtomic atoms0
                   r = Rel.transClosure $ Rel.fromList atoms
                   es = Map.foldWithKey ( \ t1 st l1 ->
                             case t1 of
                             TypeName _ _ 0 -> Set.fold ( \ t2 l2 ->
                                 case t2 of
                                 TypeName _ _ 0 -> if lesserType te t1 t2
                                     then l2 else (t1, t2) : l2
                                 _ -> l2) l1 st
                             _ -> l1) [] $ Rel.toMap r
               in return $ if null es then
                 case collapser r of
                   Result ds Nothing -> Result ds Nothing
                   Result _ (Just s2) ->
                       let s = compSubst s1 s2
                       in return (s, substC s qs,
                                  Rel.fromList $ substPairList s2 atoms0)
                 else Result (map ( \ (t1, t2) ->
                                 mkDiag Hint "rejected" $
                                             Subtyping t1 t2) es) Nothing
           Nothing -> return $ Result rs Nothing

-- | compute monotonicity of a type variable
monotonic :: Int -> Type -> (Bool, Bool)
monotonic v = foldType FoldTypeRec
  { foldTypeName = \ _ _ _ i -> (True, i /= v)
  , foldTypeAppl = \ t@(TypeAppl tf _) ~(f1, f2) (a1, a2) ->
      -- avoid evaluation of (f1, f2) if it is not needed by "~"
     case redStep t of
      Just r -> monotonic v r
      Nothing -> case rawKindOfType tf of
        FunKind CoVar _ _ _ -> (f1 && a1, f2 && a2)
        FunKind ContraVar _ _ _ -> (f1 && a2, f2 && a1)
        _ -> (f1 && a1 && a2, f2 && a1 && a2)
  , foldExpandedType = \ _ _ p -> p
  , foldTypeAbs = \ _ _ _ _ -> (False, False)
  , foldKindedType = \ _ p _ _ -> p
  , foldTypeToken = \ _ _ -> error "monotonic.foldTypeToken"
  , foldBracketType = \ _ _ _ _ -> error "monotonic.foldBracketType"
  , foldMixfixType = \ _ -> error "monotonic.foldMixfixType" }

-- | find monotonicity based instantiation
monoSubst :: Rel.Rel Type -> Type -> Subst
monoSubst r t =
    let varSet = Set.fromList . leaves (> 0)
        vs = Set.toList $ Set.union (varSet t) $ Set.unions $ map varSet
              $ Set.toList $ Rel.nodes r
        monos = filter ( \ (i, (n, rk)) -> case monotonic i t of
                                (True, _) -> isSingleton
                                    (Rel.predecessors r $
                                        TypeName n rk i)
                                _ -> False) vs
        antis = filter ( \ (i, (n, rk)) -> case monotonic i t of
                                (_, True) -> isSingleton
                                     (Rel.succs r $
                                         TypeName n rk i)
                                _ -> False) vs
        resta = filter ( \ (i, (n, rk)) -> case monotonic i t of
                                (True, True) -> hasMany $
                                     Rel.succs r $ TypeName n rk i
                                _ -> False) vs
        restb = filter ( \ (i, (n, rk)) -> case monotonic i t of
                                (True, True) -> hasMany $
                                     Rel.predecessors r $ TypeName n rk i
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
          else Map.fromDistinctAscList $ map ( \ (i, (n, rk)) ->
                (i, Set.findMin $ Rel.predecessors r $
                  TypeName n rk i)) monos
       else Map.fromDistinctAscList $ map ( \ (i, (n, rk)) ->
                (i, Set.findMin $ Rel.succs r $
                  TypeName n rk i)) antis

monoSubstsAux :: Rel.Rel Type -> Type -> Subst
monoSubstsAux r t =
    let s = monoSubst (Rel.transReduce $ Rel.irreflex r) t in
    if Map.null s then s else compSubst s
      $ monoSubstsAux (Rel.transClosure $ Rel.map (subst s) r) $ subst s t

monoSubsts :: Rel.Rel Type -> Type -> Subst
monoSubsts r t =
  let s = monoSubstsAux r t
      s2 = monoSubstsAux (Rel.fromList $ map (\ (t1, t2) -> case (t1, t2) of
        (TypeName _ _ v, TypeAppl (TypeName l _ _) t3@(TypeName _ _ v2))
          | v == 0 && l == lazyTypeId && v2 > 0 ->
              (t1, t3)
        _ -> (t1, t2)) $ Rel.toList $ Rel.map (subst s) r) t
  in compSubst s s2

-- | Downsets of type variables made monomorphic need to be considered
fromTypeVars :: LocalTypeVars -> Constraints
fromTypeVars = Map.foldWithKey
    (\ t (TypeVarDefn _ vk rk _) c -> case vk of
              Downset ty ->
                insertC (Subtyping (TypeName t rk 0) $ monoType ty) c
              _ -> c) noC

-- | the type relation of declared types
fromTypeMap :: TypeMap -> Rel.Rel Type
fromTypeMap = Map.foldWithKey (\ t ti r -> let k = typeKind ti in
                    Set.fold ( \ j -> Rel.insert (TypeName t k 0)
                                $ TypeName j k 0) r
                                    $ superTypes ti) Rel.empty
