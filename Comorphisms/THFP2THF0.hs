{-# OPTIONS -O0 #-}
{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances,
DeriveGeneric #-}
{- |
Module      :  ./Comorphisms/THFP2THF0.hs
Description :  Comorphism from THFP to THF0
Copyright   :  (c) J. von Schroeder, DFKI Bremen 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  J. von Schroeder <jonathan.von_schroeder@dfki.de>
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The comorphism from THFP to THF0.
-}

module Comorphisms.THFP2THF0 where

import Logic.Logic as Logic
import Logic.Comorphism

import Common.ProofTree
import Common.Result
import Common.Id (Token (..))
import Common.AS_Annotation (Named)

import THF.Logic_THF
import THF.Cons
import THF.Sign
import qualified THF.Sublogic as SL
import THF.As
import THF.Utils (RewriteFuns (..), rewriteSenFun, rewriteTHF0, recreateSymbols,
                  toToken, typeToTopLevelType, thfTopLevelTypeToType, mkNames)

import qualified Data.HashMap.Strict as Map
import Control.Monad (liftM)

import GHC.Generics (Generic)
import Data.Hashable

data THFP2THF0 = THFP2THF0 deriving (Show, Generic)

instance Hashable THFP2THF0

instance Language THFP2THF0

instance Comorphism THFP2THF0
                THF SL.THFSl
                BasicSpecTHF THFFormula () ()
                SignTHF MorphismTHF SymbolTHF () ProofTree
                THF SL.THFSl
                BasicSpecTHF THFFormula () ()
                SignTHF MorphismTHF SymbolTHF () ProofTree where
    sourceLogic THFP2THF0 = THF
    sourceSublogic THFP2THF0 = SL.tHFP
    targetLogic THFP2THF0 = THF
    mapSublogic THFP2THF0 _ = Just SL.tHF0
    map_theory THFP2THF0 = trans_theory
    has_model_expansion THFP2THF0 = True

trans_theory :: (SignTHF, [Named THFFormula])
                -> Result (SignTHF, [Named THFFormula])
trans_theory (sig, sentences1) = do
 let (cs_trans, sig1) = head . filter (\ (tp_t, Sign _ cs _) ->
                                  not (any (hasProdT tp_t) $ Map.elems cs)) $
                 iterate makeExplicitProducts (Map.empty, sig)
     sig2 = sig1 {consts =
      Map.map (\ c -> c {constType = curryConstType (constType c)}) $
                         consts sig1}
 sentences <- rewriteSen cs_trans sentences1
 return (recreateSymbols sig2, sentences)

type TransMap = Map.HashMap Constant [Constant]

-- note: does not do anything on non-map-types
curryConstType :: Type -> Type
curryConstType (MapType t1 t2) = prodToMapType t1 t2
curryConstType (ParType t) = ParType (curryConstType t)
curryConstType t = t

prodToMapType :: Type -> Type -> Type
prodToMapType t1 t2 = case t1 of
 MapType _ _ -> MapType (curryConstType t1) t2
 ProdType ts -> let ts' = map curryConstType ts
                in foldl (flip MapType) t2 (reverse ts')
 ParType t -> prodToMapType t t2
 _ -> MapType t1 t2

rewriteSen :: TransMap -> [Named THFFormula]
               -> Result [Named THFFormula]
rewriteSen cs_trans = mapR (rewriteSen' cs_trans)

rewriteFns :: RewriteFuns TransMap
rewriteFns = rewriteTHF0 {
 rewriteLogicFormula = rewriteLogicFormula',
 rewriteBinaryFormula =
  \ _ bf -> mkError "This function shouldn't be called!" bf,
 rewriteBinaryTuple =
  \ _ bt -> mkError "This function shouldn't be called!" bt,
 rewriteVariableList = rewriteVariableList',
 rewriteConst = rewriteConst'
}

rewriteSen' :: TransMap -> Named THFFormula
               -> Result (Named THFFormula)
rewriteSen' cs_trans = rewriteSenFun (rewriteFns, cs_trans)

rewriteLogicFormula' :: (RewriteFuns TransMap, TransMap)
                       -> THFLogicFormula -> Result THFLogicFormula
rewriteLogicFormula' d lf = case lf of
 TLF_THF_Binary_Formula bf -> do
  bf' <- rewriteBinaryFormula' d bf
  case bf' of
   Left bf'' -> return $ TLF_THF_Binary_Formula bf''
   Right uf -> return $ TLF_THF_Unitary_Formula uf
 _ -> rewriteLogicFormula rewriteTHF0 d lf

rewriteBinaryFormula' :: (RewriteFuns TransMap, TransMap)
                        -> THFBinaryFormula
                        -> Result (Either THFBinaryFormula THFUnitaryFormula)
rewriteBinaryFormula' d@(fns, _) bf = case bf of
 TBF_THF_Binary_Pair uf1 cn uf2 -> do
  uf1' <- rewriteUnitaryFormula fns d uf1
  uf2' <- rewriteUnitaryFormula fns d uf2
  case (toTuple uf1', cn, toTuple uf2') of
      (Just (TUF_THF_Tuple t1), Infix_Equality,
       Just (TUF_THF_Tuple t2)) -> if length t1 == length t2
        then return $ Left $ TBF_THF_Binary_Tuple $ TBT_THF_And_Formula $
              map (\ (t1', t2') ->
               TUF_THF_Logic_Formula_Par $ TLF_THF_Binary_Formula $
                TBF_THF_Binary_Pair (logicFormula2UnitaryFormula t1')
                 cn (logicFormula2UnitaryFormula t2')) (zip t1 t2)
        else mkError ("THFP2THF0.rewriteBinaryFormula: Equality on tuples " ++
                      "of different size!") bf
      _ -> return $ Left $ TBF_THF_Binary_Pair uf1' cn uf2'
 TBF_THF_Binary_Tuple bt -> rewriteBinaryTuple' d bt
 _ -> liftM Left $ rewriteBinaryFormula rewriteTHF0 d bf

toTuple :: THFUnitaryFormula -> Maybe THFUnitaryFormula
toTuple u@(TUF_THF_Tuple _) = Just u
toTuple (TUF_THF_Logic_Formula_Par
  (TLF_THF_Unitary_Formula u)) = Just u
toTuple _ = Nothing

logicFormula2UnitaryFormula :: THFLogicFormula -> THFUnitaryFormula
logicFormula2UnitaryFormula l = case l of
 TLF_THF_Unitary_Formula uf -> uf
 _ -> TUF_THF_Logic_Formula_Par l

rewriteBinaryTuple' :: (RewriteFuns TransMap, TransMap)
                        -> THFBinaryTuple
                        -> Result (Either THFBinaryFormula THFUnitaryFormula)
rewriteBinaryTuple' d@(fns, _) bt = case bt of
 TBT_THF_Apply_Formula ufs -> do
  ufs' <- mapR (rewriteUnitaryFormula fns d) ufs
  case ufs' of
      [] -> mkError "THFP2THF0.rewriteBinaryTuple: Illegal Application!" bt
      _ : [] -> mkError "THFP2THF0.rewriteBinaryTuple: Illegal Application!" bt
      fn : args -> case removeParensUnitaryFormula fn of
       (TUF_THF_Atom (T0A_Constant c)) ->
         case show . toToken $ c of
           'p' : 'r' : '_' : i ->
              case args of
               tuple : [] ->
                let i' = read i :: Int
                in unpack_tuple tuple i'
               _ -> mkError ("THFP2THF0.rewriteBinaryTuple: Invalid " ++
                            "argument for projection: " ++ show args) ufs
           _ -> return $ Left $ TBF_THF_Binary_Tuple $ TBT_THF_Apply_Formula $
                 fn : flattenTuples args
       TUF_THF_Tuple lfs ->
         liftM Right $ mapR (\ l ->
                         do app' <- rewriteBinaryTuple' d .
                                    TBT_THF_Apply_Formula $
                                     TUF_THF_Logic_Formula_Par l : args
                            return $ case app' of
                              Left bf -> TLF_THF_Binary_Formula bf
                              Right uf -> TLF_THF_Unitary_Formula uf) lfs
                       >>= rewriteUnitaryFormula fns d . TUF_THF_Tuple
       _ -> return $ Left $ TBF_THF_Binary_Tuple $ TBT_THF_Apply_Formula $
             fn : flattenTuples args
 _ -> liftM (Left . TBF_THF_Binary_Tuple) $ rewriteBinaryTuple rewriteTHF0 d bt

flattenTuples :: [THFUnitaryFormula] -> [THFUnitaryFormula]
flattenTuples = concatMap flattenTuple

flattenTuple :: THFUnitaryFormula -> [THFUnitaryFormula]
flattenTuple u = case removeParensUnitaryFormula u of
 TUF_THF_Tuple lfs ->
  concatMap (flattenTuple . TUF_THF_Logic_Formula_Par) lfs
 _ -> [u]

unpack_tuple :: THFUnitaryFormula -> Int
                -> Result (Either THFBinaryFormula THFUnitaryFormula)
unpack_tuple uf i = case removeParensUnitaryFormula uf of
 TUF_THF_Tuple lfs -> if i > length lfs
  then mkError "THFP2THF0.unpack_tuple: Tuple has too few elements!" uf
  else case lfs !! (i - 1) of
        TLF_THF_Binary_Formula bf -> return $ Left bf
        TLF_THF_Unitary_Formula uf' -> return $ Right uf'
        lf -> mkError ("THFP2THF0.unpack_tuple: " ++ show lf
                       ++ " is not in THF0!") uf
 _ -> mkError ("THFP2THF0.unpack_tuple: " ++ show uf ++ " is not a tuple!") uf

removeParensUnitaryFormula :: THFUnitaryFormula -> THFUnitaryFormula
removeParensUnitaryFormula (TUF_THF_Logic_Formula_Par
 (TLF_THF_Unitary_Formula uf)) = uf
removeParensUnitaryFormula uf = uf

rewriteVariableList' :: (RewriteFuns TransMap, TransMap)
                       -> [THFVariable] -> Result [THFVariable]
rewriteVariableList' (_, cs_trans) vs = do
 vs' <- mapR (\ v -> case v of
             TV_THF_Typed_Variable t tp ->
              case thfTopLevelTypeToType tp of
               Just tp' -> let cs = constMakeExplicitProduct
                                     (A_Lower_Word t) tp'
                           in mapM (\ (c, tp'') -> liftM
                                 (TV_THF_Typed_Variable (toToken c))
                                 (typeToTopLevelType (curryConstType tp''))) cs
               Nothing ->
                mkError ("THFP2THF0.rewriteVariableList: Couldn't " ++
                         "type " ++ show tp) tp
             TV_Variable t -> case transToken cs_trans t of
                               [_] -> return [v]
                               t' -> return $ map TV_Variable t') vs
 return $ concat vs'

transToken :: TransMap -> Token -> [Token]
transToken m t = case Map.toList $
  Map.filterWithKey (\ c _ -> toToken c == t) m of
                   (_, cs) : _ -> concatMap (transToken m . toToken) cs
                   [] -> [t]

rewriteConst' :: (RewriteFuns TransMap, TransMap)
                  -> Constant -> Result THFUnitaryFormula
rewriteConst' (_, m) c = case transConst' m c of
 [] -> return $ TUF_THF_Atom (T0A_Constant c)
 lfs -> return $ TUF_THF_Tuple lfs

transConst' :: TransMap -> Constant -> [THFLogicFormula]
transConst' m c = case Map.toList $
  Map.filterWithKey (\ c' _ -> c == c') m of
   (_, cs) : _ -> map (\ c' -> case transConst' m c' of
                           [] -> TLF_THF_Unitary_Formula .
                                 TUF_THF_Atom . T0A_Constant $ c'
                           lfs -> TLF_THF_Unitary_Formula .
                                  TUF_THF_Tuple $ lfs) cs
   [] -> []

constMakeExplicitProduct :: Constant -> Type -> [(Constant, Type)]
constMakeExplicitProduct c t =
 let (_, Sign _ cs _) = head . filter (\ (tp_t, Sign _ cs' _) ->
                          not (any (hasProdT tp_t) $ Map.elems cs')) $
      iterate makeExplicitProducts
      (Map.empty, Sign Map.empty (Map.fromList [(c,
        ConstInfo {constId = c, constName = N_Atomic_Word c,
                   constType = t, constAnno = Null})]) Map.empty)
 in map (\ i -> (constId i, constType i)) $ Map.elems cs

-- Note: Type definitions are non-recursive
makeExplicitProducts :: (TransMap, SignTHF) ->
 (TransMap, SignTHF)
makeExplicitProducts (cs_trans1, sig) =
 let (cs_trans, cs) = mkExplicitProductsT cs_trans1 (consts sig)
 in (cs_trans, sig {consts = cs})

mkExplicitProductsT :: TransMap -> Map.HashMap Constant ConstInfo
                       -> (TransMap, Map.HashMap Constant ConstInfo)
mkExplicitProductsT cs_trans1 cs1 = Map.foldr
 (\ c (trans, cs) -> prodTToTuple trans cs (constId c) (constName c)
                     (constType c)) (cs_trans1, cs1) cs1

prodTToTuple :: TransMap -> Map.HashMap Constant ConstInfo -> Constant
                -> Name -> Type -> (TransMap, Map.HashMap Constant ConstInfo)
prodTToTuple trans cs c n t = case t of
 MapType t1 t2 ->
  let (_, cs') = prodTToTuple Map.empty Map.empty c n t2
      cs'' = Map.delete c cs
      tuple = Map.elems cs'
      names = mkNames c n $ length tuple
  in if null tuple then (trans, cs) else
     (Map.insert c (map fst names) trans,
      foldr (\ ((n1, n2), ci) cs''' -> Map.insert n1
                ci {constName = n2,
                    constId = n1,
                    constType = MapType t1 (constType ci)} cs''')
            cs'' (zip names tuple))
 ProdType ts -> let cs' = Map.delete c cs
                    names = mkNames c n $ length ts
                in (Map.insert c (map fst names) trans,
                    foldr (\ ((n1, n2), tp) cs'' -> Map.insert n1
                              ConstInfo {constType = tp,
                                        constName = n2,
                                        constId = n1,
                                        constAnno = Null} cs'')
                          cs' (zip names ts))
 ParType tp -> prodTToTuple trans cs c n tp
 _ -> (trans, cs)

hasProdT :: TransMap -> ConstInfo -> Bool
hasProdT t = isProdT t . constType

isProdT :: TransMap -> Type -> Bool
isProdT _ TType = False
isProdT _ OType = False
isProdT _ IType = False
isProdT m (MapType _ t2) = isProdT m t2
isProdT _ (ProdType _) = True
isProdT m (CType c) = case Map.lookup c m of
                            Just _ -> True
                            Nothing -> False
isProdT _ (SType _) = False
isProdT _ (VType _) = False
isProdT m (ParType t) = isProdT m t
