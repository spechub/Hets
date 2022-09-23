{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/CASL2Prop.hs
Description :  Coding of a CASL sublogic to Propositional
Copyright   :  (c) Dominik Luecke and Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

A comorphism from CASL to Propositional. The CASL sublogic does not precisely
capture the valid domain of the translation. Sorts, ops and preds with
arguments will be ignored. The translation will fail for non-propositional
sentences.
-}

module Comorphisms.CASL2Prop (CASL2Prop (..)) where

import Common.ProofTree

import Logic.Logic
import Logic.Comorphism

-- Propositional
import qualified Propositional.Logic_Propositional as PLogic
import qualified Propositional.AS_BASIC_Propositional as PBasic
import qualified Propositional.Sublogic as PSL
import qualified Propositional.Sign as PSign
import qualified Propositional.Morphism as PMor
import qualified Propositional.Symbol as PSymbol

-- CASL
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sublogic
import CASL.Sign
import CASL.Morphism

import qualified Data.Set as Set
import qualified Data.Map as Map
import Common.AS_Annotation
import Common.Id
import Common.Result
import Common.DocUtils
import qualified Common.Lib.MapSet as MapSet
import qualified Control.Monad.Fail as Fail

-- | lid of the morphism
data CASL2Prop = CASL2Prop deriving Show

instance Language CASL2Prop where
  language_name CASL2Prop = "CASL2Propositional"

instance Comorphism CASL2Prop
    CASL
    CASL_Sublogics
    CASLBasicSpec
    CASLFORMULA
    SYMB_ITEMS
    SYMB_MAP_ITEMS
    CASLSign
    CASLMor
    Symbol
    RawSymbol
    ProofTree
    PLogic.Propositional
    PSL.PropSL
    PBasic.BASIC_SPEC
    PBasic.FORMULA
    PBasic.SYMB_ITEMS
    PBasic.SYMB_MAP_ITEMS
    PSign.Sign
    PMor.Morphism
    PSymbol.Symbol
    PSymbol.Symbol
    ProofTree
    where
      sourceLogic CASL2Prop = CASL
      sourceSublogic CASL2Prop = sublogics_max need_fol need_pred
      targetLogic CASL2Prop = PLogic.Propositional
      mapSublogic CASL2Prop = Just . mapSub
      map_theory CASL2Prop = mapTheory
      is_model_transportable CASL2Prop = True
      map_symbol CASL2Prop _ = mapSym
      map_sentence CASL2Prop _ = trForm
      map_morphism CASL2Prop = mapMor
      has_model_expansion CASL2Prop = False
      is_weakly_amalgamable CASL2Prop = True
      isInclusionComorphism CASL2Prop = False

-- | Translation of the signature
mapSig :: CASLSign -> PSign.Sign
mapSig = PSign.Sign . MapSet.keysSet
  . MapSet.filter (null . predArgs) . predMap

-- | Which is the target sublogic?
mapSub :: CASL_Sublogics -> PSL.PropSL
mapSub sl = if which_logic sl <= Horn then PSL.bottom else PSL.top

-- | Translation of morphisms
mapMor :: CASLMor -> Result PMor.Morphism
mapMor mor = return PMor.Morphism
  { PMor.source = mapSig (msource mor)
  , PMor.target = mapSig (mtarget mor)
  , PMor.propMap = Map.foldrWithKey (\ (i, pt) j ->
      if null (predArgs pt) then Map.insert i j else id) Map.empty
      $ pred_map mor }

-- | Mapping of a theory
mapTheory :: (CASLSign, [Named CASLFORMULA])
  -> Result (PSign.Sign, [Named PBasic.FORMULA])
mapTheory (sig, form) = do
  sens <- mapM trNamedForm form
  return (mapSig sig, sens)

-- | Translation of symbols
mapSym :: Symbol -> Set.Set PSymbol.Symbol
mapSym sym = case symbType sym of
  PredAsItemType pt | null $ predArgs pt ->
    Set.singleton (PSymbol.Symbol $ symName sym)
  _ -> Set.empty

-- | Helper for map theory
trNamedForm :: Named CASLFORMULA -> Result (Named PBasic.FORMULA)
trNamedForm = mapNamedM trForm

-- | Helper for map sentence and map theory
trForm :: CASLFORMULA -> Result PBasic.FORMULA
trForm form = case form of
  Negation fn rn -> do
    t <- trForm fn
    return $ PBasic.Negation t rn
  Junction j fn rn -> do
    ts <- mapM trForm fn
    return $ (case j of
      Con -> PBasic.Conjunction
      Dis -> PBasic.Disjunction) ts rn
  Relation f1 c f2 rn -> do
    t1 <- trForm f1
    t2 <- trForm f2
    return $ (if c == Equivalence then PBasic.Equivalence else
      PBasic.Implication) t1 t2 rn
  Atom b rn -> return $ (if b then PBasic.True_atom else PBasic.False_atom) rn
  Predication (Qual_pred_name pid (Pred_type [] _) _) [] _ ->
    return . PBasic.Predication . mkSimpleId $ show pid
  _ -> Fail.fail $ "not a propositional formula: " ++ showDoc form ""
