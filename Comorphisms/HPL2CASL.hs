{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/HPL2CASL.hs
Description :  Coding of hybrid popositional logic into CASL
Copyright   :  (c) Mihai Codescu, IMAR, 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.com
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

The translating comorphism from Propositional to CASL.
-}

module Comorphisms.HPL2CASL
    (
     HPL2CASL (..)
    )
    where

import Debug.Trace

import Common.ProofTree
import qualified Common.Result as Result
import qualified Common.AS_Annotation as AS_Anno
import Common.Id
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet
import qualified Data.Set as Set


import Logic.Logic
import Logic.Comorphism

-- HPL
import qualified HPL.Logic_HPL as HLogic
import qualified HPL.AS_BASIC_HPL as HBasic
import qualified Propositional.AS_BASIC_Propositional as PBasic
--import qualified HPL.Sublogic as HSL
import qualified HPL.Sign as HSign
import qualified Propositional.Sign as PSign
import qualified HPL.Morphism as HMor
import qualified HPL.Symbol as HSymbol

-- CASL
import qualified CASL.Logic_CASL as CLogic
import qualified CASL.AS_Basic_CASL as CBasic
import qualified CASL.Sublogic as CSL
import qualified CASL.Sign as CSign
import qualified CASL.Morphism as CMor
import qualified CASL.Induction as CInduction
import qualified Propositional.Prop2CASLHelpers as Helpers

-- | lid of the morphism
data HPL2CASL = HPL2CASL deriving Show

instance Language HPL2CASL where
  language_name HPL2CASL = "HybridPropositional2CASL"

instance Comorphism HPL2CASL
    HLogic.HPL
    ()--PSL.PropSL
    HBasic.BASIC_SPEC
    HBasic.FORMULA
    PBasic.SYMB_ITEMS
    PBasic.SYMB_MAP_ITEMS
    HSign.HSign
    HMor.HMorphism
    HSymbol.Symbol
    HSymbol.Symbol
    () --ProofTree
    CLogic.CASL
    CSL.CASL_Sublogics
    CLogic.CASLBasicSpec
    CBasic.CASLFORMULA
    CBasic.SYMB_ITEMS
    CBasic.SYMB_MAP_ITEMS
    CSign.CASLSign
    CMor.CASLMor
    CSign.Symbol
    CMor.RawSymbol
    ProofTree
    where
      sourceLogic HPL2CASL = HLogic.HPL
      sourceSublogic HPL2CASL = ()
      targetLogic HPL2CASL = CLogic.CASL
      -- mapSublogic HPL2CASL = error "nyi1"--Just . mapSub
      map_theory HPL2CASL = mapTheory
      --is_model_transportable HPL2CASL = True
      map_symbol HPL2CASL _ = error "nyi4"--mapSym
      map_sentence HPL2CASL = error "nyi5"--mapSentence
      map_morphism HPL2CASL = error "nyi6"--mapMor
      -- has_model_expansion HPL2CASL = True
      -- is_weakly_amalgamable HPL2CASL = True
      isInclusionComorphism HPL2CASL = False

mapSign :: HSign.HSign -> CSign.CASLSign
  -- no constraints, so C(\Delta) is empty
  -- to work generic, mapSign should also give a list of sentences
mapSign sig = let 
  st = genName "state"
  opsMap = foldl
            (\m i -> MapSet.insert i (CSign.OpType CBasic.Total [] st) m)
            MapSet.empty 
            $ Set.toList $ HSign.noms sig
  pSig = (CSign.emptySign ())
              { CSign.sortRel = Rel.insertKey st $ Rel.empty
              , CSign.opMap = opsMap
              , CSign.predMap = Set.fold (`MapSet.insert` CSign.PredType [st])
                                MapSet.empty $ PSign.items $ HSign.propSig sig
              }
  lambdaSig = pSig { 
                CSign.predMap = MapSet.insert (genName "lambda") 
                                              (CSign.PredType [st, st]) $
                                              CSign.predMap pSig
               }
 in lambdaSig

stSort :: Id
stSort = genName "state"

mapSen :: HBasic.FORMULA -> CBasic.CASLFORMULA
mapSen sen = 
 let sen' = mapSenAux (genNumVar "x" 0) True sen
 in CBasic.Quantification
      CBasic.Universal 
      [CBasic.Var_decl [genNumVar "x" 0] stSort nullRange]
      sen'
      nullRange
      

mapSenAux :: Token -> Bool -> HBasic.FORMULA -> CBasic.CASLFORMULA
 -- b is True for gn_x0 and false for nominals in at sentences
mapSenAux x b frm = case frm of
 HBasic.Prop_formula (PBasic.Predication tok) ->
    CBasic.mkPredication 
       (CBasic.mkQualPred (mkId [tok]) $ 
                          CBasic.Pred_type [stSort] nullRange)
       [if b then CBasic.mkVarTerm x stSort  
             else CBasic.mkAppl 
                    (CBasic.Qual_op_name 
                          (simpleIdToId x) 
                          (CBasic.Op_type CBasic.Total [] stSort nullRange) 
                          nullRange) 
                    [] 
       ]
 HBasic.Nominal tok _ -> 
    CBasic.Equation 
       (CBasic.mkVarTerm x stSort) 
       CBasic.Strong 
       (CBasic.Application 
          (CBasic.Qual_op_name (mkId [tok]) 
              (CBasic.Op_type CBasic.Total [] stSort nullRange)
           nullRange
          )
          [] nullRange) 
       nullRange
 HBasic.Negation frm' _ -> CBasic.Negation (mapSenAux x b frm') nullRange
 HBasic.Conjunction sens _ -> 
     CBasic.Junction CBasic.Con (map (mapSenAux x b) sens) nullRange
 HBasic.Disjunction sens _ -> 
     CBasic.Junction CBasic.Dis (map (mapSenAux x b) sens) nullRange
 HBasic.Implication sen1 sen2 _ -> 
     CBasic.Relation (mapSenAux x b sen1) 
           CBasic.Implication (mapSenAux x b sen2) nullRange
 HBasic.Equivalence sen1 sen2 _ -> 
     CBasic.Relation (mapSenAux x b sen1) 
           CBasic.Equivalence (mapSenAux x b sen2) nullRange
 HBasic.AtState tok frm' _ ->
     mapSenAux tok False frm' 
 HBasic.BoxFormula frm' _ -> let
     y = genNumVar "y" 0 
     lambdaXY = CBasic.mkPredication 
                  (CBasic.Qual_pred_name 
                     (genName "lambda") 
                     (CBasic.Pred_type [stSort, stSort] nullRange) 
                     nullRange)
                  [CBasic.Qual_var x stSort nullRange, 
                   CBasic.Qual_var y stSort nullRange]  
     implSen =  CBasic.Relation lambdaXY CBasic.Implication
                                (mapSenAux y b frm') nullRange
     declY = CBasic.Var_decl [genNumVar "y" 0] stSort nullRange --TODO: int arg? 
  in CBasic.mkForall [declY] implSen
 HBasic.DiamondFormula frm' _ -> let
     y = genNumVar "y" 0 
     lambdaXY = CBasic.mkPredication 
                  (CBasic.Qual_pred_name 
                     (genName "lambda") 
                     (CBasic.Pred_type [stSort, stSort] nullRange) 
                     nullRange)
                  [CBasic.Qual_var x stSort nullRange, 
                   CBasic.Qual_var y stSort nullRange]  
     andSen =  CBasic.Junction CBasic.Con 
                               [lambdaXY, mapSenAux y b frm'] 
                               nullRange
     declY = CBasic.Var_decl [genNumVar "y" 0] stSort nullRange --TODO: int arg? 
  in CBasic.mkExist [declY] andSen 
 _ -> CBasic.Atom True nullRange
   

mapTheory :: (HSign.HSign, [AS_Anno.Named HBasic.FORMULA])
  -> Result.Result (CSign.CASLSign, [AS_Anno.Named CBasic.CASLFORMULA])
mapTheory (sig, form) = Result.Result [] $
    Just (mapSign sig, map (AS_Anno.mapNamed mapSen) form)

