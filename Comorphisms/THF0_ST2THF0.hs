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

module Comorphisms.THF0_ST2THF0 where

import Logic.Logic as Logic
import Logic.Comorphism

import Common.ProofTree
import Common.Result
import Common.AS_Annotation (Named,SenAttr(..))

import THF.Logic_THF
import THF.Cons
import THF.Sign
import qualified THF.Sublogic as SL
import THF.As
import THF.StaticAnalysisTHF (thfTopLevelTypeToType)
import THF.Utils

import qualified Data.Map as Map

import Control.Monad (foldM)

data THF0_ST2THF0 = THF0_ST2THF0 deriving Show

instance Language THF0_ST2THF0

instance Comorphism THF0_ST2THF0
                THF SL.THFSl
                BasicSpecTHF SentenceTHF () ()
                SignTHF MorphismTHF SymbolTHF () ProofTree
                THF SL.THFSl
                BasicSpecTHF SentenceTHF () ()
                SignTHF MorphismTHF SymbolTHF () ProofTree where
    sourceLogic THF0_ST2THF0 = THF
    sourceSublogic THF0_ST2THF0 = SL.tHF0_ST
    targetLogic THF0_ST2THF0 = THF
    mapSublogic THF0_ST2THF0 _ = Just SL.tHF0
    map_theory THF0_ST2THF0 = trans_theory
    has_model_expansion THF0_ST2THF0 = True

trans_theory :: (SignTHF,[Named SentenceTHF])
                -> Result (SignTHF,[Named SentenceTHF])
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
  c' <- numbered c
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

rewriteSen :: TransMap -> Named SentenceTHF -> Result (Named SentenceTHF)
rewriteSen tp_trans sen = do
 let sen_ = sentence sen
 sen' <- case senFormula . sentence $ sen of
             TF_THF_Logic_Formula lf ->
               rewriteLogicFormula tp_trans lf
                >>= return . TF_THF_Logic_Formula
             T0F_THF_Typed_Const  tc ->
               rewriteTypedConst tp_trans tc
                >>= return . T0F_THF_Typed_Const
             a@(TF_THF_Sequent _) ->
              mkError "THF0_ST2THF0.rewriteSen: Sequents are not in THF0!" a
 return $ sen { sentence = sen_ { senFormula = sen' } }

rewriteLogicFormula :: TransMap -> THFLogicFormula -> Result THFLogicFormula
rewriteLogicFormula tp_trans lf = case lf of
 TLF_THF_Binary_Formula bf -> do
  bf' <- rewriteBinaryFormula tp_trans bf
  return $ TLF_THF_Binary_Formula bf'
 TLF_THF_Unitary_Formula uf ->
   rewriteUnitaryFormula tp_trans uf
    >>= return . TLF_THF_Unitary_Formula
 TLF_THF_Type_Formula _ ->
  mkError ("THF0_ST2THF0.rewriteLogicFormula: TLF_THF_Type_Formula " ++ 
          "is not in THF0!") lf
 TLF_THF_Sub_Type _ ->
  mkError ("THF0_ST2THF0.rewriteLogicFormula: TLF_THF_Sub_Type " ++
          "is not in THF0!") lf

rewriteTypedConst :: TransMap -> THFTypedConst -> Result THFTypedConst
rewriteTypedConst tp_trans tc = case tc of
 T0TC_Typed_Const c tlf ->
  case thfTopLevelTypeToType tlf of
    Just t -> return $ T0TC_Typed_Const c $ typeToTopLevelType
     (simplifyType tp_trans t)
    Nothing ->
     mkError ("THF0_ST2THF0.rewriteTypedConst: Couldn't interpret type for " ++
           "Constant " ++ show c) tlf
 T0TC_THF_TypedConst_Par tc' ->
   rewriteTypedConst tp_trans tc'
    >>= return . T0TC_THF_TypedConst_Par

rewriteBinaryFormula :: TransMap -> THFBinaryFormula -> Result THFBinaryFormula
rewriteBinaryFormula tp_trans bf = case bf of
 TBF_THF_Binary_Type _ -> mkError
  "THF0_ST2THF0.rewriteBinaryFormula: TBF_THF_Binary_Type is not in THF0!" bf
 TBF_THF_Binary_Pair uf1 cn uf2 -> do
  uf1' <- rewriteUnitaryFormula tp_trans uf1
  uf2' <- rewriteUnitaryFormula tp_trans uf2
  return $ TBF_THF_Binary_Pair uf1' cn uf2'
 TBF_THF_Binary_Tuple bt -> rewriteBinaryTuple tp_trans bt

rewriteBinaryTuple :: TransMap -> THFBinaryTuple -> Result THFBinaryFormula
rewriteBinaryTuple tp_trans bt = case bt of
 TBT_THF_Or_Formula ufs -> do
  ufs' <- mapR (rewriteUnitaryFormula tp_trans) ufs
  return $ TBF_THF_Binary_Tuple $ TBT_THF_Or_Formula ufs'
 TBT_THF_And_Formula ufs -> do
  ufs' <- mapR (rewriteUnitaryFormula tp_trans) ufs
  return $ TBF_THF_Binary_Tuple $ TBT_THF_And_Formula $ ufs'
 TBT_THF_Apply_Formula ufs -> do
  mapR (rewriteUnitaryFormula tp_trans) ufs
   >>= return . TBF_THF_Binary_Tuple . TBT_THF_Apply_Formula

rewriteUnitaryFormula :: TransMap -> THFUnitaryFormula
                         -> Result THFUnitaryFormula
rewriteUnitaryFormula tp_trans uf = case uf of
 TUF_THF_Conditional _ _ _ ->
  mkError ("THF0_ST2THF0.rewriteUnitaryFormula: " ++
           "TUF_THF_Conditional is not in THF0!") uf
 TUF_THF_Quantified_Formula qf -> case qf of
  TQF_THF_Quantified_Formula q vs uf' -> do
   vs' <- rewriteVariableList tp_trans vs
   uf'' <- rewriteUnitaryFormula tp_trans uf'
   return $ TUF_THF_Quantified_Formula $ TQF_THF_Quantified_Formula q vs' uf''
  T0QF_THF_Quantified_Var q vs uf' -> do
   vs' <- rewriteVariableList tp_trans vs
   uf'' <- rewriteUnitaryFormula tp_trans uf'
   return $ TUF_THF_Quantified_Formula $ T0QF_THF_Quantified_Var q vs' uf''
  T0QF_THF_Quantified_Novar q uf' -> do
   uf'' <- rewriteUnitaryFormula tp_trans uf'
   return $ TUF_THF_Quantified_Formula $ T0QF_THF_Quantified_Novar q uf''
 TUF_THF_Unary_Formula c lf ->
  rewriteLogicFormula tp_trans lf
   >>= return . (TUF_THF_Unary_Formula c)
 TUF_THF_Atom a -> return . TUF_THF_Atom $ a
 TUF_THF_Tuple t -> mapR (rewriteLogicFormula tp_trans) t
  >>= return . TUF_THF_Tuple
 TUF_THF_Logic_Formula_Par lf ->
  rewriteLogicFormula tp_trans lf
   >>= return . TUF_THF_Logic_Formula_Par
 T0UF_THF_Abstraction vs uf' -> do
  vs' <- rewriteVariableList tp_trans vs
  uf'' <- rewriteUnitaryFormula tp_trans uf'
  return $ T0UF_THF_Abstraction vs' uf''

rewriteVariableList :: TransMap -> [THFVariable] -> Result [THFVariable]
rewriteVariableList tp_trans vs = 
 mapR (\v -> case v of
             TV_THF_Typed_Variable t tp ->
              case thfTopLevelTypeToType tp of
               Just tp' -> return $
                TV_THF_Typed_Variable t
                 (typeToTopLevelType (simplifyType tp_trans tp'))
               Nothing -> mkError ("THFP2THF0.rewriteVariableList: Couldn't " ++
                                   "analyze type " ++ show tp) tp
             TV_Variable t -> return $ TV_Variable t) vs
