{- |
Module      :  $Header$
Description :  Coding of a CASL sublogic to Propositional
Copyright   :  (c) Dominik Luecke and Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

a comorphism from CASL to Propositional.
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
      map_symbol CASL2Prop = mapSym
      map_sentence CASL2Prop _ = return . trForm
      map_morphism CASL2Prop = mapMor
      has_model_expansion CASL2Prop = True
      is_weakly_amalgamable CASL2Prop = True
      isInclusionComorphism CASL2Prop = True

-- | Translation of the signature
mapSig :: CASLSign -> PSign.Sign
mapSig = PSign.Sign . Map.keysSet . Map.filter (not . Set.null)
  . Map.map (Set.filter (null . predArgs)) . predMap

-- | Which is the target sublogic?
mapSub :: CASL_Sublogics -> PSL.PropSL
mapSub sl = if which_logic sl <= Horn then PSL.bottom else PSL.top

-- | Translation of morphisms
mapMor :: CASLMor -> Result PMor.Morphism
mapMor mor = return PMor.Morphism
  { PMor.source = mapSig (msource mor)
  , PMor.target = mapSig (mtarget mor)
  , PMor.propMap = Map.foldWithKey (\ (i, pt) j ->
      if null (predArgs pt) then Map.insert i j else id) Map.empty
      $ pred_map mor }

-- | Mapping of a theory
mapTheory :: (CASLSign, [Named CASLFORMULA])
  -> Result (PSign.Sign, [Named PBasic.FORMULA])
mapTheory (sig, form) = return (mapSig sig, map trNamedForm form)

-- | Translation of symbols
mapSym :: Symbol -> Set.Set PSymbol.Symbol
mapSym sym = case symbType sym of
  PredAsItemType pt | null $ predArgs pt ->
    Set.singleton (PSymbol.Symbol $ symName sym)
  _ -> Set.empty

-- | Helper for map theory
trNamedForm :: Named CASLFORMULA -> Named PBasic.FORMULA
trNamedForm = mapNamed trForm

-- | Helper for map sentence and map theory
trForm :: CASLFORMULA -> PBasic.FORMULA
trForm form = case form of
  Negation fn rn -> PBasic.Negation (trForm fn) rn
  Conjunction fn rn -> PBasic.Conjunction (map trForm fn) rn
  Disjunction fn rn -> PBasic.Disjunction (map trForm fn) rn
  Implication f1 f2 b rn -> let
    t1 = trForm f1
    t2 = trForm f2
    in if b then PBasic.Implication t1 t2 rn else PBasic.Implication t2 t1 rn
  Equivalence f1 f2 rn ->
                PBasic.Equivalence (trForm f1) (trForm f2) rn
  True_atom rn -> PBasic.True_atom rn
  False_atom rn -> PBasic.False_atom rn
  Predication (Qual_pred_name pid (Pred_type [] _) _) [] _ ->
    PBasic.Predication $ mkSimpleId $ show pid
  _ -> error $ "not a propositional formula: " ++ showDoc form ""
