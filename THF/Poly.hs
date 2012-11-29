{- |
Module      :  $Header$
Description :  Helper functions for coding out polymorphism
Copyright   :  (c) J. von Schroeder, DFKI Bremen 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Jonathan von Schroeder <j.von_schroeder@dfki.de>
Stability   :  provisional
Portability :  non-portable

-}
module THF.Poly
where

import THF.Cons
import THF.Sign
import THF.Utils
import THF.As
import THF.StaticAnalysisTHF (thfTopLevelTypeToType)

import Common.Result
import Common.Id
import Common.AS_Annotation

import Control.Monad.State
import qualified Data.Map (Map, lookup, insert, empty,
                           mapAccumWithKey, foldrWithKey,
                           mapWithKey)
import qualified Data.List (mapAccumL, elemIndex)

occursType :: Token -> Type -> Bool
occursType t tp = case tp of
 MapType tp1 tp2 ->
  occursType t tp1 || occursType t tp2
 ProdType tps ->
  any (occursType t) tps
 VType t1 -> t == t1
 ParType tp2 -> occursType t tp2
 _ -> False

unifyType :: Type -> Type -> Result [(Token, Type)]
unifyType tp1 tp2 = case (tp1, tp2) of
    (ParType tp1', _) ->
     unifyType tp1' tp2
    (_, ParType tp2') ->
     unifyType tp1 tp2'
    (VType t1, VType t2) -> return $
     if t1 == t2 then [] else [(t1, tp2)]
    (VType t1, _) -> if occursType t1 tp2
     then mkError "Occurs check failed!" t1
     else return [(t1, tp2)]
    (_, VType t2) -> if occursType t2 tp1
     then mkError "Occurs check failed!" t2
     else return [(t2, tp1)]
    (MapType tp1_1 tp1_2,
     MapType tp2_1 tp2_2) -> do
     u1 <- unifyType tp1_1 tp2_1
     u2 <- unifyType tp1_2 tp2_2
     return $ u1 ++ u2
    (MapType _ _, _) ->
     mkError ("Different type constructor!" ++
      show (tp1, tp2)) nullRange
    (_, MapType _ _) ->
     mkError ("Different type constructor!" ++
      show (tp1, tp2)) nullRange
    (ProdType tps1, ProdType tps2) ->
     if length tps1 == length tps2 then
      liftM concat $
       mapR (uncurry unifyType) (zip tps1 tps2)
     else mkError "Products of different size!" nullRange
    (ProdType _, _) ->
     mkError ("Different type constructor!" ++
      show (tp1, tp2)) nullRange
    (CType c1,CType c2) -> if c1 == c2
     then return [] else mkError ("Cannot unify different kinds "
      ++ show c1 ++ show c2) nullRange
    (CType _,_) -> mkError "Unification not possible!" nullRange
    (_,CType _) -> mkError "Unification not possible!" nullRange
    (_, ProdType _) ->
     mkError ("Different type constructor!" ++
      show (tp1, tp2)) nullRange
    _ -> return []

applyType :: [(Token, Type)] -> Token -> Maybe Type
applyType us t = case us of
 (t', tp) : _ | t' == t -> Just tp
 _ : us' -> applyType us' t
 _ -> Nothing

apply :: [(Token, Type)] -> Type -> Type
apply us t = case t of
 ParType t' -> ParType $ apply us t'
 MapType t1 t2 -> MapType (apply us t1)
  (apply us t2)
 ProdType tps -> ProdType $ map (apply us) tps
 VType tok -> case applyType us tok of
  Just t' -> apply us t'
  Nothing -> t
 _ -> t

unify' :: [(Type, Type)] -> Result [(Token, Type)]
unify' ts = case ts of
 [] -> return []
 (t1, t2) : ts' -> do
  r1 <- unify' ts'
  let t1' = apply r1 t1
  let t2' = apply r1 t2
  r2 <- unifyType t1' t2'
  return (r1 ++ r2)

tmpV :: Token
tmpV = mkSimpleId "tmpV"

type Constraints = UniqueT Maybe (Type, [(Type, Type)])

getTypeC :: ConstMap -> THFFormula -> Constraints
getTypeC cm f = case f of
 TF_THF_Logic_Formula lf -> getTypeCLF cm lf
 _ -> lift Nothing

getTypeCLF :: ConstMap -> THFLogicFormula -> Constraints
getTypeCLF cm lf = case lf of
 TLF_THF_Binary_Formula bf -> getTypeCBF cm bf
 TLF_THF_Unitary_Formula uf -> getTypeCUF cm uf
 _ -> lift Nothing

getTypeCBF :: ConstMap -> THFBinaryFormula -> Constraints
getTypeCBF cm bf = case bf of
 TBF_THF_Binary_Pair uf1 c uf2 -> if (case c of
  Infix_Equality -> True
  Infix_Inequality -> True
  _ -> False) then do
   (t1, cs1) <- getTypeCUF cm uf1
   (t2, cs2) <- getTypeCUF cm uf2
   return (OType,
    cs1 ++ cs2 ++ [(t1, t2)])
  else do
   (t1, cs1) <- getTypeCUF cm uf1
   (t2, cs2) <- getTypeCUF cm uf2
   return (OType,
    cs1 ++ cs2 ++ [(t1, OType), (t2, OType)])
 TBF_THF_Binary_Tuple bt ->
  let ufs = case bt of
       TBT_THF_Or_Formula ufs' -> ufs'
       TBT_THF_And_Formula ufs' -> ufs'
       TBT_THF_Apply_Formula ufs' -> ufs'
  in case bt of
      TBT_THF_Apply_Formula _ -> do
       ufs' <- mapM (getTypeCUF cm) ufs
       case ufs' of
        [] -> lift Nothing
        _ : [] -> lift Nothing
        u : ufs'' -> do
         let (t1, cs1) = u
             tps = map fst ufs''
             cs2 = map snd ufs''
         {- try to do a best-effort beta-reduction
             * either t1 is a "function type" we
               can recognize
             * or we simply assign a new type variable
               and hope that further constraints
               will determine the type variable -}
         t <- applyResult (length ufs'') t1
         return (t, cs1 ++ concat cs2
          ++ [(t1, genFn $ tps ++ [t])])
      _ -> do
       ufs' <- mapM (getTypeCUF cm) ufs
       case ufs' of
        [] -> lift Nothing
        (t,cs) : [] -> return (t,cs++[(t,OType)])
        _ -> do
         let (ts,cs) = unzip ufs'
         return (OType,concat cs ++ map (\t -> (t,OType)) ts)
 _ -> lift Nothing

applyResult :: Int -> Type -> UniqueT Maybe Type
applyResult 0 t = return t
applyResult i t = case t of
 MapType _ t' -> applyResult (i - 1) t'
 _ -> do
  v <- numberedTok tmpV
  return (VType v)

getTypeCUF :: ConstMap -> THFUnitaryFormula -> Constraints
getTypeCUF cm uf = case uf of
 TUF_THF_Quantified_Formula qf -> case qf of
  TQF_THF_Quantified_Formula _ vs uf' -> getTypeCQF vs uf'
  T0QF_THF_Quantified_Var _ vs uf' -> getTypeCQF vs uf'
  _ -> lift Nothing
  where getTypeCQF vs uf' = do
         cm' <- foldM (\ cm' v ->
          case v of
           TV_THF_Typed_Variable t tp ->
            lift (thfTopLevelTypeToType tp)
             >>= \ tp' -> return $ ins t tp' cm'
           TV_Variable t -> do
            v' <- numberedTok tmpV
            return $ ins t (VType v') cm') cm vs
         (t, cs) <- getTypeCUF cm' uf'
         return (t, cs ++ [(t, OType)])
        c = A_Single_Quoted
        ins t tp = Data.Map.insert (c t)
          ConstInfo {
            constId = c t,
            constName = N_Atomic_Word $ c t,
            constType = tp,
            constAnno = Null}
 TUF_THF_Unary_Formula _ lf -> do
  (lf', cs) <- getTypeCLF cm lf
  return (lf', cs ++ [(lf', OType)])
 TUF_THF_Atom a -> case a of
  TA_THF_Conn_Term _ -> lift Nothing
  T0A_Constant c -> case Data.Map.lookup c cm of
   Just ti -> return (constType ti, [])
   Nothing -> do
    v <- numberedTok tmpV
    return (VType v, [])
  -- fixme - add types for internal constants
  T0A_Defined_Constant _ -> lift Nothing
  T0A_System_Constant _ -> lift Nothing
  T0A_Variable v -> case Data.Map.lookup (A_Single_Quoted v) cm of
   Just ti -> return (constType ti, [])
   Nothing -> do
    v' <- numberedTok tmpV
    return (VType v', [])
  _ -> lift Nothing
 TUF_THF_Tuple lfs -> do
  lfs' <- mapM (getTypeCLF cm) lfs
  let (tps, cs) = unzip lfs'
  return (ProdType tps, concat cs)
 TUF_THF_Logic_Formula_Par lf -> getTypeCLF cm lf
 T0UF_THF_Abstraction vs uf' -> do
  (vst, cm') <- foldM (\ (l, cm') v ->
          case v of
           TV_THF_Typed_Variable t tp ->
            lift (thfTopLevelTypeToType tp)
             >>= \ tp' -> return (tp' : l, ins t tp' cm')
           TV_Variable t -> do
            v' <- numberedTok tmpV
            return (VType v' : l, ins t (VType v') cm')) ([], cm) vs
  (uf'', cs) <- getTypeCUF cm' uf'
  case vst of
   [] -> lift Nothing
   _ : [] -> lift Nothing
   _ -> return (genFn (vst ++ [uf'']), cs)
  where c = A_Single_Quoted
        ins t tp = Data.Map.insert (c t)
                 ConstInfo {
                   constId = c t,
                   constName = N_Atomic_Word $ c t,
                   constType = tp,
                   constAnno = Null }
 _ -> lift Nothing

genFn :: [Type] -> Type
genFn (tp : []) = tp
genFn (tp : tps) = MapType tp (genFn tps)
genFn _ = error "This shouldn't happen!"

insertAndIdx :: (Ord a, Eq b) => Data.Map.Map a [b] -> a -> b
                 -> (Data.Map.Map a [b], Int)
insertAndIdx m k v = case Data.Map.lookup k m of
 Just l -> case Data.List.elemIndex v l of
  Just i -> (m, i)
  Nothing -> (Data.Map.insert k (l ++ [v]) m, length l)
 Nothing -> (Data.Map.insert k [v] m, 0)

intToStr :: Int -> String
intToStr 0 = ""
intToStr i = '_' : show i

flattenMap :: Data.Map.Map Constant [a] -> Data.Map.Map Constant a
flattenMap = Data.Map.foldrWithKey
 (\ k v new_m ->
  let ks = evalUnique $ replicateM (length v) $ do
       f <- fresh
       let s = intToStr $ fromIntegral (f - 1)
       return $ addSuffix s k
  in foldl (\ new_m' (k', v') -> Data.Map.insert k' v' new_m')
      new_m (zip ks v)) Data.Map.empty

type RewriteArg = Data.Map.Map Constant Int

rewriteVariableList' :: (RewriteFuns RewriteArg, RewriteArg) ->
                        [THFVariable] -> Result [THFVariable]
rewriteVariableList' (_, cm) vs = return $
 map (\ v -> let t = case v of
                     TV_THF_Typed_Variable t' _ -> t'
                     TV_Variable t' -> t'
            in case Data.Map.lookup (A_Single_Quoted t) cm of
                Just i -> TV_Variable $
                 t { tokStr = tokStr t ++ intToStr i }
                Nothing -> v) vs

rewriteConst' :: (RewriteFuns RewriteArg, RewriteArg) ->
                 Constant -> Result THFUnitaryFormula
rewriteConst' (_, cm) c = return . TUF_THF_Atom . T0A_Constant $
 case Data.Map.lookup c cm of
  Just i -> addSuffix (intToStr i) c
  Nothing -> c

{- Note: Only Works if all Types are simple,
   i.e. there are no ShortTypes -}
infer :: ConstMap -> [Named THFFormula]
          -> Result (ConstMap, [Named THFFormula])
infer cm fs =
 let constraints' = mapM (evalUniqueT . getTypeC cm
      . sentence) fs
     constraints =
      liftM (map (\ (t, cs) -> (OType, t) : cs)) constraints'
     unifications =
      liftM (map unify') constraints
 in case unifications of
     Just unis' -> sequence unis' >>= \ unis ->
      let (cm', instances) = Data.List.mapAccumL
           (\ cm'_ u ->
             let (cm'', m1) = Data.Map.mapAccumWithKey
                  (\ cm''' c ci -> insertAndIdx cm''' c
                     (apply u (constType ci))) cm'_ cm
             in (cm'', m1))
           Data.Map.empty unis
          new_cm = Data.Map.mapWithKey (\ k v ->
           ConstInfo { constId = k,
                       constName = N_Atomic_Word k,
                       constType = v,
                       constAnno = Null}) $ flattenMap cm'
      in do
           let r = rewriteTHF0 {
             rewriteVariableList = rewriteVariableList',
             rewriteConst = rewriteConst'
           }
           fs' <- mapM (\ (f, i) -> rewriteSenFun (r, i) f)
            (zip fs instances)
           return (new_cm, fs')
     Nothing -> mkError "Failed to generate constraints!" nullRange
