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
import Control.Monad (liftM,mapM)
import Control.Monad.State
import qualified Data.Map (Map,lookup,insert,map,empty,
                           mapAccumWithKey,foldWithKey,
                           mapWithKey)
import qualified Data.Set as Set
import qualified Data.List (mapAccumL,elemIndex)

occursKind :: Token -> Kind -> Bool
occursKind t k = case k of
 MapKind k1 k2 ->
  (occursKind t k1) || (occursKind t k2)
 ProdKind ks -> or $
  map (occursKind t) ks
 VKind t1 -> t == t1
 ParKind k -> occursKind t k
 _ -> False

occursType :: Token -> Type -> Bool
occursType t tp = case tp of
 MapType tp1 tp2 ->
  (occursType t tp1) || (occursType t tp2)
 ProdType tps -> or $
  map (occursType t) tps
 VType t1 -> t == t1
 ParType tp2 -> (occursType t tp2)
 _ -> False

data Unification = UniKind Kind | UniType Type

unifyKind :: Kind -> Kind -> Result [(Token,Unification)]
unifyKind k1 k2 = case (k1,k2) of
    (ParKind k1',_) ->
     (unifyKind k1' k2)
    (_,ParKind k2') ->
     (unifyKind k1 k2')
    (VKind t1, VKind t2) -> return $
     if t1 == t2 then [] else [(t1,UniKind k2)]
    (VKind t1,_) -> if occursKind t1 k2
     then mkError "Occurs check failed!" t1
     else return [(t1,UniKind k2)]
    (_,VKind t2) -> if occursKind t2 k1
     then mkError "Occurs check failed!" t2
     else return [(t2,UniKind k1)]
    (MapKind k1_1 k1_2,
     MapKind k2_1 k2_2) -> do
      u1 <- (unifyKind k1_1 k2_1)
      u2 <- (unifyKind k1_2 k2_2)
      return $ u1 ++ u2
    (MapKind _ _,_) ->
     mkError ("Different type constructor! " ++
              show (k1,k2)) nullRange
    (_,MapKind _ _) ->
     mkError ("Different type constructor! " ++
              show (k1,k2)) nullRange
    (ProdKind ks1, ProdKind ks2) ->
     if length ks1 == length ks2 then
      (liftM concat) $
       mapR (uncurry unifyKind) (zip ks1 ks2)
     else mkError "Products of different size!" nullRange
    (ProdKind _,_) -> 
     mkError ("Different type constructor! " ++
              show (k1,k2)) nullRange
    (_,ProdKind _) ->
     mkError ("Different type constructor! " ++
              show (k1,k2)) nullRange
    _ -> return []

unifyType :: TypeMap -> Type -> Type -> Result [(Token,Unification)]
unifyType tm tp1 tp2 = case (tp1,tp2) of
    (ParType tp1',_) ->
     (unifyType tm tp1' tp2)
    (_,ParType tp2') ->
     (unifyType tm tp1 tp2')
    (VType t1, VType t2) -> return $
     if t1 == t2 then [] else [(t1,UniType tp2)]
    (VType t1,_) -> if occursType t1 tp2
     then mkError "Occurs check failed!" t1
     else return [(t1,UniType tp2)]
    (_,VType t2) -> if occursType t2 tp1
     then mkError "Occurs check failed!" t2
     else return [(t2,UniType tp1)]
    (MapType tp1_1 tp1_2,
     MapType tp2_1 tp2_2) -> do
     u1 <- (unifyType tm tp1_1 tp2_1)
     u2 <- (unifyType tm tp1_2 tp2_2)
     return $ u1 ++ u2
    (MapType _ _,_) ->
     mkError ("Different type constructor!" ++
      show (tp1,tp2)) nullRange
    (_,MapType _ _) ->
     mkError ("Different type constructor!" ++
      show (tp1,tp2)) nullRange
    (ProdType tps1, ProdType tps2) ->
     if length tps1 == length tps2 then
      (liftM concat) $
       mapR (uncurry (unifyType tm)) (zip tps1 tps2)
     else mkError "Products of different size!" nullRange
    (ProdType _,_) ->
     mkError ("Different type constructor!" ++
      show (tp1,tp2)) nullRange
    (_,ProdType _) ->
     mkError ("Different type constructor!" ++
      show (tp1,tp2)) nullRange
    (CType c1,CType c2) -> if c1 == c2 then return []
     else case (Data.Map.lookup c1 tm,Data.Map.lookup c2 tm) of
           (Just ti1, Just ti2) ->
            unifyKind (typeKind ti1) (typeKind ti2)
           _ -> mkError "" nullRange
    _ -> return []

applyKind' :: [(Token,Unification)] -> Token -> Maybe Kind
applyKind' us t = case us of
 (t',UniKind k):_ | t' == t -> Just k
 _:us' -> applyKind' us' t
 _ -> Nothing

applyKind :: [(Token,Unification)] -> Kind -> Kind
applyKind us k = case k of
 ParKind k' -> ParKind $ applyKind us k'
 MapKind k1 k2 -> MapKind (applyKind us k1)
  (applyKind us k2)
 ProdKind ks -> ProdKind $ map (applyKind us) ks
 VKind t -> case applyKind' us t of
  Just k'-> applyKind us k'
  Nothing -> k
 _ -> k

applyType :: [(Token,Unification)] -> Token -> Maybe Type
applyType us t = case us of
 (t',UniType tp):_ | t' == t -> Just tp
 _:us' -> applyType us' t
 _ -> Nothing

apply :: [(Token,Unification)] -> Type -> Type
apply us t = case t of
 ParType t' -> ParType $ apply us t'
 MapType t1 t2 -> MapType (apply us t1)
  (apply us t2)
 ProdType tps -> ProdType $ map (apply us) tps
 VType tok -> case applyType us tok of
  Just t' -> apply us t'
  Nothing -> t
 _ -> t

unify' :: TypeMap -> [(Type,Type)]
           -> Result [(Token,Unification)]
unify' tm ts = case ts of
 [] -> return []
 (t1,t2) : ts' -> do
  r1 <- unify' tm ts'
  let t1' = apply r1 t1
  let t2' = apply r1 t2
  let tm' = Data.Map.map (\ti ->
       ti { typeKind = applyKind r1 $ typeKind ti }) tm
  r2 <- unifyType tm' t1' t2'
  return (r1 ++ r2)

tmpV = mkSimpleId "tmpV"

type Constraints = UniqueT Maybe (Type,[(Type,Type)])

getTypeC :: ConstMap -> THFFormula -> Constraints
getTypeC cm f = case f of
 TF_THF_Logic_Formula lf -> getTypeCLF cm lf
 _ -> lift Nothing

getTypeCLF :: ConstMap -> THFLogicFormula -> Constraints
getTypeCLF cm lf = case lf of
 TLF_THF_Binary_Formula bf  -> getTypeCBF cm bf
 TLF_THF_Unitary_Formula uf -> getTypeCUF cm uf
 _ -> lift Nothing

getTypeCBF :: ConstMap -> THFBinaryFormula -> Constraints
getTypeCBF cm bf = case bf of
 TBF_THF_Binary_Pair uf1 c uf2 -> if (case c of
  Infix_Equality   -> True
  Infix_Inequality -> True
  _ -> False) then do
   (t1,cs1) <- getTypeCUF cm uf1
   (t2,cs2) <- getTypeCUF cm uf2
   return (OType,
    cs1++cs2++[(t1,t2)])
  else do
   (t1,cs1) <- getTypeCUF cm uf1
   (t2,cs2) <- getTypeCUF cm uf2
   return (OType,
    cs1++cs2++[(t1,OType),(t2,OType)])
 TBF_THF_Binary_Tuple bt ->
  let ufs = case bt of
       TBT_THF_Or_Formula ufs    -> ufs
       TBT_THF_And_Formula ufs   -> ufs
       TBT_THF_Apply_Formula ufs -> ufs
  in case bt of
      TBT_THF_Apply_Formula _ -> do
       ufs' <- mapM (getTypeCUF cm) ufs
       case ufs' of
        [] -> lift Nothing
        _:[] -> lift Nothing
        u:ufs'' -> do
         let (t1,cs1) = u
             tps = map fst ufs''
             cs2 = map snd ufs''
         {- try to do a best-effort beta-reduction
             * either t1 is a "function type" we 
               can recognize
             * or we simply assign a new type variable
               and hope that further constraints
               will determine the type variable -}
         t <- applyResult (length ufs'') t1
         return (t,cs1++(concat cs2)
          ++[(t1,genFn $ tps ++ [t])])
      _ -> lift Nothing
 _ -> lift Nothing

applyResult :: Int -> Type -> UniqueT Maybe Type
applyResult 0 t = return t
applyResult i t = case t of
 MapType _ t' -> applyResult (i-1) t'
 _ -> do
  v <- numberedTok tmpV
  return (VType v)

getTypeCUF :: ConstMap -> THFUnitaryFormula -> Constraints
getTypeCUF cm uf = case uf of
 TUF_THF_Quantified_Formula qf -> case qf of
  TQF_THF_Quantified_Formula q vs uf' -> getTypeCQF cm q vs uf'
  T0QF_THF_Quantified_Var q vs uf'    -> getTypeCQF cm q vs uf'
  _ -> lift Nothing
  where getTypeCQF cm q vs uf' = do
         cm' <- foldM (\cm' v ->
          case v of
           TV_THF_Typed_Variable t tp ->
            lift (thfTopLevelTypeToType tp)
             >>= \tp' -> return $ ins t tp' cm'
           TV_Variable t -> do
            v <- numberedTok tmpV
            return $ ins t (VType v) cm') cm vs
         (t,cs) <- getTypeCUF cm' uf'
         return (t,cs++[(t,OType)])
        c t = A_Single_Quoted t
        ins t tp cm' = Data.Map.insert (c t)
          (ConstInfo {
            constId = c t,
            constName = N_Atomic_Word $ c t,
            constType = tp,
            constAnno = Null}) cm'
 TUF_THF_Unary_Formula c lf -> do
  (lf',cs) <- getTypeCLF cm lf
  return (lf',cs++[(lf',OType)])
 TUF_THF_Atom a -> case a of
  TA_THF_Conn_Term c -> lift Nothing
  T0A_Constant c -> case Data.Map.lookup c cm of
   Just ti -> return (constType ti,[])
   Nothing -> do
    v <- numberedTok tmpV
    return (VType $ v,[])
  {- fixme - add types for internal constants -}
  T0A_Defined_Constant c -> lift Nothing
  T0A_System_Constant c -> lift Nothing
  T0A_Variable v -> case Data.Map.lookup (A_Single_Quoted v) cm of
   Just ti -> return (constType ti,[])
   Nothing -> do
    v <- numberedTok tmpV
    return (VType $ v,[])
  _ -> lift Nothing
 TUF_THF_Tuple lfs -> do
  lfs' <- sequence $ map (getTypeCLF cm) lfs
  let (tps,cs) = unzip lfs'
  return (ProdType tps,concat cs)
 TUF_THF_Logic_Formula_Par lf -> getTypeCLF cm lf
 T0UF_THF_Abstraction vs uf' -> do
  (vst,cm') <- foldM (\(l,cm') v ->
          case v of
           TV_THF_Typed_Variable t tp ->
            lift (thfTopLevelTypeToType tp)
             >>= \tp' -> return $ (tp':l,ins t tp' cm')
           TV_Variable t -> do
            v <- numberedTok tmpV
            return $ ((VType v):l,ins t (VType v) cm')) ([],cm) vs
  (uf'',cs) <- getTypeCUF cm' uf'
  case vst of
   [] -> lift Nothing
   _:[] -> lift Nothing
   _ -> return (genFn (vst++[uf'']),cs)
  where c t = A_Single_Quoted t
        ins t tp cm' = Data.Map.insert (c t)
                 (ConstInfo {
                   constId = c t,
                   constName = N_Atomic_Word $ c t,
                   constType = tp,
                   constAnno = Null }) cm'
 _ -> lift Nothing

genFn :: [Type] -> Type
genFn (tp:[])  = tp
genFn (tp:tps) = MapType tp (genFn tps)

insertAndIdx :: (Ord a,Eq b) => Data.Map.Map a [b] -> a -> b
                 -> (Data.Map.Map a [b], Int)
insertAndIdx m k v = case Data.Map.lookup k m of
 Just l  -> case Data.List.elemIndex v l of
  Just i  -> (m,i)
  Nothing -> (Data.Map.insert k (l++[v]) m,length l)
 Nothing -> (Data.Map.insert k [v] m,0)

intToStr :: Int -> String
intToStr 0 = ""
intToStr i = "_" ++ show i

flattenMap :: Data.Map.Map Constant [a] -> Data.Map.Map Constant a
flattenMap m = Data.Map.foldWithKey
 (\k v new_m ->
  let ks = evalUnique $ replicateM (length v) $ do
       f <- fresh
       let s = intToStr $ fromIntegral (f-1)
       return $ addSuffix s k
  in foldl (\new_m' (k',v') -> Data.Map.insert k' v' new_m')
      new_m (zip ks v)) Data.Map.empty m

type RewriteArg = (Data.Map.Map Constant Int,
                   Data.Map.Map Constant Int)

rewriteVariableList' :: (RewriteFuns RewriteArg, RewriteArg) -> 
                        [THFVariable] -> Result [THFVariable]
rewriteVariableList' (_,(cm,tm)) vs = return $
 map (\v -> let t = case v of
                     TV_THF_Typed_Variable t _ -> t
                     TV_Variable t -> t
            in case Data.Map.lookup (A_Single_Quoted t) cm of
                Just i -> TV_Variable $
                 t { tokStr = (tokStr t) ++ intToStr i }
                Nothing -> v) vs

rewriteConst' :: (RewriteFuns RewriteArg, RewriteArg) ->
                 Constant -> Result THFUnitaryFormula
rewriteConst' (_,(cm,tm)) c = return . TUF_THF_Atom . T0A_Constant $
 case Data.Map.lookup c cm of
  Just i -> addSuffix (intToStr i) c
  Nothing -> c

infer :: ConstMap -> TypeMap -> [Named THFFormula]
          -> Result (ConstMap, TypeMap, [Named THFFormula])
infer cm tm fs = 
 let constraints' = sequence $ map (evalUniqueT . getTypeC cm
      . sentence) fs
     constraints  = constraints'
      >>= return . map (\(t,cs) -> (OType,t):cs)
     unifications = constraints
      >>= return . map (unify' tm)
 in case unifications of
     Just unis' -> sequence unis' >>= \unis -> 
      let ((cm',tm'),instances) = Data.List.mapAccumL
           (\(cm',tm') u -> 
             let (cm'', m1) = Data.Map.mapAccumWithKey
                  (\cm'' c ci -> insertAndIdx cm'' c
                     (apply u (constType ci))) cm' cm
                 (tm'', m2) = Data.Map.mapAccumWithKey
                  (\tm'' c ti -> insertAndIdx tm'' c
                     (applyKind u (typeKind ti))) tm' tm
             in ((cm'',tm''),(m1,m2)))
           (Data.Map.empty,Data.Map.empty) unis
          new_cm = Data.Map.mapWithKey (\k v -> 
           ConstInfo { constId = k,
                       constName = N_Atomic_Word $ k,
                       constType = v,
                       constAnno = Null}) $ flattenMap cm'
          new_tm = Data.Map.mapWithKey (\k v -> 
           TypeInfo { THF.Sign.typeId = k,
                      typeName = N_Atomic_Word $ k,
                      typeKind = v,
                      typeAnno = Null}) $ flattenMap tm'
      in do
           let r = rewriteTHF0 {
             rewriteVariableList = rewriteVariableList',
             rewriteConst = rewriteConst'
           }
           fs' <- sequence $ map (\(f,i) -> rewriteSenFun (r,i) f) (zip fs instances)
           return (new_cm,new_tm,fs')
     Nothing -> mkError "Failed to generate constraints!" nullRange
