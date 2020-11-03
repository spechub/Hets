{- |
Module      :  ./THF/Poly.hs
Description :  Helper functions for coding out polymorphism
Copyright   :  (c) J. von Schroeder, DFKI Bremen 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Jonathan von Schroeder <jonathan.von_schroeder@dfki.de>
Stability   :  provisional
Portability :  non-portable

-}
module THF.Poly
where

import THF.Cons
import THF.Sign
import THF.Utils
import THF.As
import THF.PrintTHF ()
import THF.Print ()

import Common.Result
import Common.Id
import Common.AS_Annotation
import Common.DocUtils

import Control.Monad.State
import qualified Data.HashMap.Strict (HashMap, lookup, insert, empty,
                           foldrWithKey,
                           mapWithKey, toList, fromList) 
import qualified Data.List (mapAccumL, elemIndex)
import qualified Data.Set (fromList, toList)
import Data.Maybe (catMaybes)

import Data.Hashable

sh :: Pretty a => a -> String
sh = show . pretty

data Constraint = NormalC (String, Range, Type)
                | WeakC (String, Range, Type) deriving Show

instance GetRange Constraint where
    getRange (NormalC (_, r, _)) = r
    getRange (WeakC (_, r, _)) = r

instance GetRange Type where
    getRange _ = nullRange

occursType :: Token -> Type -> Bool
occursType t tp = case tp of
 MapType tp1 tp2 ->
  occursType t tp1 || occursType t tp2
 ProdType tps ->
  any (occursType t) tps
 VType t1 -> t == t1
 ParType tp2 -> occursType t tp2
 _ -> False

constraintToType :: Constraint -> (Bool, (String, Range, Type))
constraintToType (WeakC d) = (True, d)
constraintToType (NormalC d) = (False, d)

toConstraint :: Bool -> (String, Range, Type) -> Constraint
toConstraint weak = if weak then WeakC
                    else NormalC

unifyType :: Type -> Constraint -> Result [(Token, Type)]
unifyType tp1 tp2_ =
 let (weak, (s, r, tp2)) = constraintToType tp2_
     c t = toConstraint weak (s, r, t)
 in case (tp1, tp2) of
     (ParType tp1', _) ->
      unifyType tp1' (c tp2)
     (_, ParType tp2') ->
      unifyType tp1 (c tp2')
     (VType t1, VType t2) -> return $
      if t1 == t2 then [] else [(t1, tp2)]
     (VType t1, _) -> if occursType t1 tp2
      then fatal_error ("Occurs check failed! - "
       ++ s) r
      else return [(t1, tp2)]
     (_, VType t2) -> if occursType t2 tp1
      then fatal_error ("Occurs check failed! - "
       ++ s) r
      else return [(t2, tp1)]
     (MapType tp1_1 tp1_2,
      MapType tp2_1 tp2_2) -> do
      u1 <- unifyType tp1_1 (c tp2_1)
      u2 <- unifyType tp1_2 (c tp2_2)
      return $ u1 ++ u2
     (MapType _ _, _) ->
      fatal_error ("Different type constructors! " ++
       " - " ++ s) r
     (_, MapType _ _) ->
      fatal_error ("Different type constructors! " ++
       " - " ++ s) r
     (ProdType tps1, ProdType tps2) ->
      if length tps1 == length tps2 ||
         weak then
       liftM concat $
        mapR (\ (tp1', tp2') -> unifyType tp1' (c tp2'))
         (zip tps1 tps2)
      else fatal_error ("Products of different size! - " ++ s) r
     (ProdType _, _) ->
      fatal_error ("Different type constructors! - " ++ s) r
     (CType c1, CType c2) -> if c1 == c2
      then return [] else fatal_error ("Cannot unify different kinds!" ++ s) r
     (CType _, _) -> fatal_error ("Unification not possible! - " ++ s) r
     (_, CType _) -> fatal_error ("Unification not possible! - " ++ s) r
     (_, ProdType _) ->
      fatal_error ("Different type constructors! - " ++ s) r
     (TType, TType) -> return []
     (OType, OType) -> return []
     (IType, IType) -> return []
     (TType, _) -> fatal_error ("Cannot unify TType with "
      ++ show tp2 ++ "! - " ++ s) r
     (_, TType) -> fatal_error ("Cannot unify TType with "
      ++ show tp1 ++ "! - " ++ s) r
     (OType, _) -> fatal_error ("Cannot unify OType with "
      ++ show tp2 ++ "! - " ++ s) r
     (_, OType) -> fatal_error ("Cannot unify OType with "
      ++ show tp1 ++ "! - " ++ s) r
     (IType, _) -> fatal_error ("Cannot unify IType with "
      ++ show tp2 ++ "! - " ++ s) r
     (_, IType) -> fatal_error ("Cannot unify IType with "
      ++ show tp1 ++ "! - " ++ s) r
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

unify' :: [(Type, Constraint)] -> Result [(Token, Type)]
unify' ts = case ts of
 [] -> return []
 (t1, t2) : ts' -> do
  r1 <- unify' ts'
  let t1' = apply r1 t1
  let (weak, (msg, rg, t2'')) = constraintToType t2
  let t2' = apply r1 t2''
  r2 <- unifyType t1' (toConstraint weak (msg, rg, t2'))
  return (r1 ++ r2)

tmpV :: Token
tmpV = mkSimpleId "tmpV"

type Constraints = UniqueT Result (Type, [(Type, Constraint)])

not_supported :: (Show a, GetRange a) => a -> Constraints
not_supported f = lift $ fatal_error
                   ("Formula " ++ show f ++ " not supported!")
                   (getRange f)

getTypeC :: ConstMap -> THFFormula -> Constraints
getTypeC cm f = case f of
 TF_THF_Logic_Formula lf -> getTypeCLF cm lf
 _ -> not_supported f

getTypeCLF :: ConstMap -> THFLogicFormula -> Constraints
getTypeCLF cm lf = case lf of
 TLF_THF_Binary_Formula bf -> getTypeCBF cm bf
 TLF_THF_Unitary_Formula uf -> getTypeCUF cm uf
 _ -> not_supported lf

getTypeCBF :: ConstMap -> THFBinaryFormula -> Constraints
getTypeCBF cm bf = case bf of
 TBF_THF_Binary_Pair uf1 c uf2 -> if (case c of
  Infix_Equality -> True
  Infix_Inequality -> True
  _ -> False) then do
   (t1, cs1) <- getTypeCUF cm uf1
   (t2, cs2) <- getTypeCUF cm uf2
   let errMsg = "(In-)Equality requires (" ++
        sh uf1 ++ ") : (" ++ sh t1
        ++ ") and (" ++ sh uf2 ++ ") : ("
        ++ sh t2 ++ ") to have the same type"
   return (OType,
    cs1 ++ cs2 ++ [(t1, NormalC (errMsg, getRangeSpan bf, t2))])
  else do
   (t1, cs1) <- getTypeCUF cm uf1
   (t2, cs2) <- getTypeCUF cm uf2
   let errMsg1 = "Infix operator " ++ sh c
        ++ " requires (" ++ sh uf1 ++ ") : ("
        ++ sh t1 ++ ")  to have type OType"
   let errMsg2 = "Infix operator " ++ sh c
        ++ " requires (" ++ sh uf2 ++ ") : ("
        ++ sh t2 ++ ")  to have type OType"
   return (OType,
    cs1 ++ cs2 ++ [(t1, NormalC (errMsg1, getRangeSpan uf1, OType)),
                   (t2, NormalC (errMsg2, getRangeSpan uf2, OType))])
 TBF_THF_Binary_Tuple bt ->
  let ufs = case bt of
       TBT_THF_Or_Formula ufs' -> ufs'
       TBT_THF_And_Formula ufs' -> ufs'
       TBT_THF_Apply_Formula ufs' -> ufs'
  in case bt of
      TBT_THF_Apply_Formula _ -> do
       ufs' <- mapM (getTypeCUF cm) ufs
       case ufs' of
        [] -> lift $ fatal_error ("Invalid Application: "
                                  ++ show bt) (getRange bt)
        _ : [] -> lift $ fatal_error ("Invalid Application: "
                                      ++ show bt) (getRange bt)
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
         let errMsg = "Application is not well typed"
         return (t, cs1 ++ concat cs2
          ++ [(t1, WeakC (errMsg, getRangeSpan bt, genFn $ tps ++ [t]))])
      _ -> do
       ufs' <- mapM (getTypeCUF cm) ufs
       case ufs' of
        [] -> lift $ fatal_error ("Empty boolean connective: "
                           ++ show bt) (getRange bt)
        (t, cs) : [] -> return (t, cs ++ [(t, NormalC (
         "Boolean connective requires all " ++
         "arguments to be of type OType", getRangeSpan ufs, OType))])
        _ -> do
         let (ts, cs) = unzip ufs'
         let errMsg = "Boolean connective requires all " ++
                      "arguments to be of type OType"
         return (OType, concat cs ++ map (\ t ->
          (t, NormalC (errMsg, getRangeSpan bt, OType))) ts)
 _ -> not_supported bf

applyResult :: Int -> Type -> UniqueT Result Type
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
  _ -> not_supported uf
  where getTypeCQF vs uf' = do
         cm' <- foldM (\ cm' v ->
          case v of
           TV_THF_Typed_Variable t tp -> case thfTopLevelTypeToType tp of
             Just tp' -> return $ ins t tp' cm'
             Nothing ->
              lift $ fatal_error ("Failed to analyze type " ++ show tp)
                                 (getRange tp)
           TV_Variable t -> do
            v' <- numberedTok tmpV
            return $ ins t (VType v') cm') cm vs
         (t, cs) <- getTypeCUF cm' uf'
         let errMsg = "Quantified Formula (" ++ sh uf' ++ ") : ("
                      ++ sh t ++ ") is expected to be of type OType"
         return (t, cs ++ [(t, NormalC (errMsg, getRangeSpan uf', OType))])
        c = A_Single_Quoted
        ins t tp = Data.HashMap.Strict.insert (c t)
          ConstInfo {
            constId = c t,
            constName = N_Atomic_Word $ c t,
            constType = tp,
            constAnno = Null}
 TUF_THF_Unary_Formula q lf -> do
  (lf', cs) <- getTypeCLF cm lf
  let errMsg = "Unary Formula (" ++ sh uf ++ ") : ("
               ++ sh uf ++ ") is expected to be of type OType"
      lf'' = case q of
              Negation -> lf'
              _ -> case lf' of
                     MapType _ t -> t
                     _ ->  error "TUF_THF_Unary_Formula"
  return (lf'', cs ++ [(lf'', NormalC (errMsg, getRangeSpan uf, OType))])
 TUF_THF_Atom a -> case a of
  TA_THF_Conn_Term c -> case c of
   TCT_THF_Unary_Connective cn -> case cn of
    Negation -> return (MapType OType OType,[])
    _ -> do
                    v <- numberedTok tmpV
                    return (MapType (MapType (VType v) OType) OType,[])
   TCT_Assoc_Connective _ -> return (MapType OType (MapType OType OType),[])
   TCT_THF_Pair_Connective _ -> return (MapType OType (MapType OType OType),[])
   _ -> not_supported a
  T0A_Constant c -> case Data.HashMap.Strict.lookup c cm of
   Just ti -> return (constType ti, [])
   Nothing -> case show $ toToken c of
     'p' : 'r' : '_' : i' -> do
      let i = read i' :: Int
      vs <- replicateM i $ liftM VType $ numberedTok tmpV
      return (MapType (ProdType vs) $ last vs, [])
     _ -> do
      v <- numberedTok tmpV
      return (VType v, [])
  -- fixme - add types for internal constants
  T0A_Defined_Constant c -> if (show c) == "true" || (show c) == "false"
   then return (OType, [])
   else not_supported a
  T0A_System_Constant _ -> not_supported a
  T0A_Variable v -> case Data.HashMap.Strict.lookup (A_Single_Quoted v) cm of
   Just ti -> return (constType ti, [])
   Nothing -> do
    v' <- numberedTok tmpV
    return (VType v', [])
  _ -> not_supported a
 TUF_THF_Tuple lfs -> do
  lfs' <- mapM (getTypeCLF cm) lfs
  let (tps, cs) = unzip lfs'
  return (ProdType tps, concat cs)
 TUF_THF_Logic_Formula_Par lf -> getTypeCLF cm lf
 T0UF_THF_Abstraction vs uf' -> do
  (vst, cm') <- foldM (\ (l, cm') v ->
          case v of
           TV_THF_Typed_Variable t tp ->
            case thfTopLevelTypeToType tp of
             Just tp' -> return (tp' : l, ins t tp' cm')
             Nothing ->
              lift $ fatal_error ("Failed to analyze type " ++ show tp)
                                 (getRange tp)
           TV_Variable t -> do
            v' <- numberedTok tmpV
            return (VType v' : l, ins t (VType v') cm')) ([], cm) (reverse vs)
  (uf'', cs) <- getTypeCUF cm' uf'
  case vst of
   [] -> lift $ fatal_error ("Invalid Abstraction: "
                             ++ show uf) (getRange uf)
   _ -> return (genFn (vst ++ [uf'']), cs)
  where c = A_Single_Quoted
        ins t tp = Data.HashMap.Strict.insert (c t)
                 ConstInfo {
                   constId = c t,
                   constName = N_Atomic_Word $ c t,
                   constType = tp,
                   constAnno = Null }
 _ -> not_supported uf

genFn :: [Type] -> Type
genFn (tp : []) = tp
genFn (tp : tps) = MapType tp (genFn tps)
genFn _ = error "This shouldn't happen!"

insertAndIdx :: (Ord a, Eq b, Hashable a) => Data.HashMap.Strict.HashMap a [b] -> a -> b
                 -> (Data.HashMap.Strict.HashMap a [b], Maybe Int)
insertAndIdx m k v = case Data.HashMap.Strict.lookup k m of
 Just l -> case Data.List.elemIndex v l of
  Just i -> (m, Just i)
  Nothing -> (Data.HashMap.Strict.insert k (l ++ [v]) m,
   Just $ length l)
 Nothing -> (Data.HashMap.Strict.insert k [v] m, Just 0)

intToStr :: Int -> String
intToStr 0 = ""
intToStr i = '_' : show i

flattenMap :: Data.HashMap.Strict.HashMap Constant [a] -> Data.HashMap.Strict.HashMap Constant a
flattenMap = Data.HashMap.Strict.foldrWithKey
 (\ k v new_m ->
  let ks = evalUnique $ replicateM (length v) $ do
       f <- fresh
       let s = intToStr $ fromIntegral (f - 1)
       return $ addSuffix s k
  in foldl (\ new_m' (k', v') -> Data.HashMap.Strict.insert k' v' new_m')
      new_m (zip ks v)) Data.HashMap.Strict.empty

type RewriteArg = Data.HashMap.Strict.HashMap Constant (Maybe Int)

rewriteVariableList_ :: (RewriteFuns RewriteArg, RewriteArg) ->
                        [THFVariable] -> Result [THFVariable]
rewriteVariableList_ (_, cm) vs = return $
 map (\ v -> let t = case v of
                     TV_THF_Typed_Variable t' _ -> t'
                     TV_Variable t' -> t'
            in case Data.HashMap.Strict.lookup (A_Single_Quoted t) cm of
                Just (Just i) -> TV_Variable $
                 t { tokStr = tokStr t ++ intToStr i }
                _ -> v) vs

rewriteConst_ :: (RewriteFuns RewriteArg, RewriteArg) ->
                 Constant -> Result THFUnitaryFormula
rewriteConst_ (_, cm) c = return . TUF_THF_Atom . T0A_Constant $
 case Data.HashMap.Strict.lookup c cm of
  Just (Just i) -> addSuffix (intToStr i) c
  _ -> c

rewriteConst4needsConst :: (RewriteFuns Constant, Constant) ->
                           Constant -> Result THFUnitaryFormula
rewriteConst4needsConst (_, c1) c2 =
 if c1 == c2 then mkError "" nullRange
 else return . TUF_THF_Atom . T0A_Constant $ c2

needsConst :: Constant -> Named THFFormula -> Bool
needsConst c f =
 let r = rewriteTHF0 {rewriteConst = rewriteConst4needsConst}
     res = rewriteSenFun (r, c) f
 in case resultToMaybe res of
     Nothing -> True
     _ -> False

infer :: ConstMap -> [Named THFFormula]
          -> Result (ConstMap, [Named THFFormula])
infer cm fs =
 let constraints' = mapM (evalUniqueT . getTypeC cm
      . sentence) fs
     errMsg = "Sentences have to be of type OType"
     constraints =
      liftM (map (\ (t, cs) -> (OType, NormalC
       (errMsg, getRangeSpan cs, t)) : cs)) constraints'
 in do
  unis' <- liftM (map unify') constraints
  sequence unis' >>= \ unis ->
      let (cm', instances) = Data.List.mapAccumL
           (\ cm'_ (f, u) ->
             let (cm'', m1) = mapAccumWithKey
                  (\ cm''' c ci -> if needsConst c f
                     then insertAndIdx cm''' c
                           (apply u (constType ci))
                     else (cm''', Nothing)) cm'_ cm
             in (cm'', m1))
           Data.HashMap.Strict.empty (zip fs unis)
          new_cm = Data.HashMap.Strict.mapWithKey (\ k v ->
           ConstInfo { constId = k,
                       constName = N_Atomic_Word k,
                       constType = v,
                       constAnno = Null}) $ flattenMap cm'
      in do
           let r = rewriteTHF0 {
             rewriteVariableList = rewriteVariableList_,
             rewriteConst = rewriteConst_
           }
           fs' <- mapM (\ (f, i) -> rewriteSenFun (r, i) f)
            (zip fs instances)
           return (new_cm, fs')

mapAccumWithKey :: (Hashable k, Eq k) => 
   (a -> k -> b -> (a,c)) -> a -> Data.HashMap.Strict.HashMap k b -> 
   (a, Data.HashMap.Strict.HashMap k c)
mapAccumWithKey f acc hm1 = 
 let hl1 = Data.HashMap.Strict.toList hm1
     (acc', hl2) = foldl (\(a, l2) (k, b) -> let (a', c) = f a k b in (a', (k, c):l2)) (acc, []) hl1 -- TODO: should sort hl1!
 in (acc', Data.HashMap.Strict.fromList hl2)

typeConstsOf :: Type -> [Constant]
typeConstsOf (MapType tp1 tp2) = (typeConstsOf tp1) ++ (typeConstsOf tp2)
typeConstsOf (ProdType tps) = concat $ map typeConstsOf tps
typeConstsOf (CType c) = [c]
typeConstsOf (ParType t) = typeConstsOf t
typeConstsOf _ = []

collectVariableTypes :: (AnaFuns a Constant, a) -> [THFVariable] -> Result [Constant]
collectVariableTypes _ vs =
 let tps = catMaybes $ map (\v -> case v of
                                   TV_THF_Typed_Variable _ t ->
                                    thfTopLevelTypeToType t 
                                   _ -> Nothing) vs
 in return . concat $ map typeConstsOf tps

getSymbols :: SignTHF -> THFFormula -> [SymbolTHF]
getSymbols s f =
 let f' = makeNamed "tmp" f
     cs = Data.HashMap.Strict.toList $ fst $ propagateErrors "THF.Poly.getSymbols" $
                            infer (consts s) [f']
     r = anaTHF0 { anaVariableList = collectVariableTypes }
     ts' = propagateErrors "THF.Poly.getSymbols" $ anaSenFun (r, []) f'
     ts = Data.Set.toList . Data.Set.fromList $ ts' ++
          (concat (map (typeConstsOf . constType . snd) cs))
     symsC = map (\(_,ci) -> Symbol { symId = constId ci,
                                      symName = constName ci,
                                      symType = ST_Const $ constType ci }) cs
     symsT = map (\n -> case Data.HashMap.Strict.lookup n (types s) of
                         Just t -> Symbol { symId = THF.Sign.typeId t,
                                            symName = typeName t,
                                            symType = ST_Type Kind}
                         Nothing -> error $ "THF.Poly.getSymbols: " ++
                                            "Unknown type " ++ (show n)) ts
 in symsC ++ symsT

type_check :: TypeMap -> ConstMap -> [Named THFFormula]
               -> Result [[(Token, Type)]]
type_check _ cm sens = do
 let constraints' = mapM (evalUniqueT .
      getTypeC cm . sentence) sens
 let errMsg = "Every formula is expected to be of type OType"
 let constraints =
      liftM (map (\ (t, cs) -> (OType, NormalC (errMsg, nullRange, t)) : cs))
            constraints'
 unifications <- liftM (map unify') constraints
 sequence unifications
