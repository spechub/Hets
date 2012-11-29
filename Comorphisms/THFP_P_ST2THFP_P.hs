{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Comorphism removing syntactic sugar
Copyright   :  (c) J. von Schroeder, DFKI Bremen 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  J. von Schroeder <j.von_schroeder@dfki.de>
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

Remove the syntactic sugar provided by the ShortTypes extension
-}

module Comorphisms.THFP_P_ST2THFP_P where

import Logic.Logic as Logic
import Logic.Comorphism

import Common.ProofTree
import Common.Result
import Common.AS_Annotation (Named)

import THF.Logic_THF
import THF.Cons
import THF.Sign
import qualified THF.Sublogic as SL
import THF.As
import THF.StaticAnalysisTHF (thfTopLevelTypeToType)
import THF.Utils

import qualified Data.Map as Map

import Control.Monad (foldM)

data THFP_P_ST2THFP_P = THFP_P_ST2THFP_P deriving Show

instance Language THFP_P_ST2THFP_P

instance Comorphism THFP_P_ST2THFP_P
                THF SL.THFSl
                BasicSpecTHF THFFormula () ()
                SignTHF MorphismTHF SymbolTHF () ProofTree
                THF SL.THFSl
                BasicSpecTHF THFFormula () ()
                SignTHF MorphismTHF SymbolTHF () ProofTree where
    sourceLogic THFP_P_ST2THFP_P = THF
    sourceSublogic THFP_P_ST2THFP_P = SL.tHF0_P_ST
    targetLogic THFP_P_ST2THFP_P = THF
    mapSublogic THFP_P_ST2THFP_P _ = Just SL.tHF0_P
    map_theory THFP_P_ST2THFP_P = trans_theory
    has_model_expansion THFP_P_ST2THFP_P = True

trans_theory :: (SignTHF,[Named THFFormula])
                -> Result (SignTHF,[Named THFFormula])
trans_theory (sig, sentences1) = do
 let (tp_trans,sig2) = rewriteTypes sig
     sig1 = case sig2 of
      Sign _ cs _ ->
       sig2 {consts = Map.map (\ci -> ci {constType =
        simplifyType tp_trans $ constType ci}) cs}
 sentences <- mapR (rewriteSen tp_trans) sentences1
 return (recreateSymbols sig1, sentences)

type TransMap = Map.Map Constant Type

rewriteTypes :: SignTHF -> (TransMap, SignTHF)
rewriteTypes s =
 let (trans,types') = Map.foldlWithKey
      (\(m,t) k v -> case typeKind v of
         Kind -> (m,Map.insert k v t)
         k' -> let (tp,t') = evalUnique $ rewriteKind k t k'
               in (Map.insert k tp m,t'))
      (Map.empty,Map.empty) $ types s
 in (trans,s { types = types' })

insertType :: Constant -> Kind -> TypeMap -> TypeMap
insertType c k =
 Map.insert c
  (TypeInfo { typeId   = c,
              typeName = N_Atomic_Word c,
              typeKind = k,
              typeAnno = Null })
       

rewriteKind :: Constant -> TypeMap -> Kind -> Unique (Type,TypeMap)
rewriteKind c tp_map k = case k of
 Kind -> do
  c' <- Unique $ numbered c
  return (CType c',insertType c' Kind tp_map)
 MapKind k1 k2 -> do
  (t1,tp_map')   <- rewriteKind c tp_map k1
  (t2,tp_map'') <- rewriteKind c tp_map' k2
  return (MapType t1 t2,tp_map'')
 ProdKind ks -> do
  (ts',tp_map') <- foldM (\(ts,tp_map'') k' ->
    do
     (t,tp_map''') <- rewriteKind c tp_map'' k'
     return (t:ts,tp_map'''))
   ([],tp_map) (reverse ks)
  return (ProdType ts',tp_map')
 SysType t -> return (SType t,tp_map)
 VKind t -> return (VType t,tp_map)
 ParKind k' -> do
  (t,tp_map') <- rewriteKind c tp_map k'
  return (ParType t,tp_map')

simplifyType :: TransMap -> Type -> Type
simplifyType trans_map t = case t of
 MapType t1 t2 -> MapType (simplifyType trans_map t1)
                          (simplifyType trans_map t2)
 ProdType ts -> ProdType (map (simplifyType trans_map) ts)
 CType c -> case Map.lookup c trans_map of
  Just t' -> t'
  Nothing -> t
 ParType t' -> ParType (simplifyType trans_map t')
 _ -> t

rewriteFns :: RewriteFuns TransMap
rewriteFns = rewriteTHF0 {
 rewriteVariableList = rewriteVariableList'
}

rewriteSen :: TransMap -> Named THFFormula -> Result (Named THFFormula)
rewriteSen tp_trans = rewriteSenFun (rewriteFns,tp_trans)

rewriteVariableList' :: (RewriteFuns TransMap,TransMap) -> [THFVariable]
                         -> Result [THFVariable]
rewriteVariableList' (_,tp_trans) vs = 
 mapR (\v -> case v of
             TV_THF_Typed_Variable t tp ->
              case thfTopLevelTypeToType tp of
               Just tp' -> (typeToTopLevelType (simplifyType tp_trans tp'))
                >>= return . TV_THF_Typed_Variable t
               Nothing -> mkError ("THFP2THF0.rewriteVariableList: Couldn't " ++
                                   "analyze type " ++ show tp) tp
             TV_Variable t -> return $ TV_Variable t) vs
