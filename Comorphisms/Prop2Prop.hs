{- |
Module      :  $Header$
Description :  Coding of CASL into SoftFOL
Copyright   :  (c) Dominik Luecke and Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@tzi.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Translations from Propositional to its sublogics.
-}

module Comorphisms.Prop2Prop
    where

import Logic.Logic
import Logic.Comorphism
import qualified Data.Set as Set
import qualified Common.Result as Result
import qualified Propositional.Prop2CNF as P2C


-- Propositional
import qualified Propositional.Logic_Propositional as PLogic
import qualified Propositional.AS_BASIC_Propositional as PBasic
import qualified Propositional.Sublogic as PSL
import qualified Propositional.Sign as PSign
import qualified Propositional.Morphism as PMor
import qualified Propositional.Symbol as PSymbol

-- | lids of the morphisms

data Prop2CNF = Prop2CNF deriving (Show)


instance Language Prop2CNF

instance Comorphism Prop2CNF
    PLogic.Propositional                -- lid 1
    PSL.PropSL                          -- sublogics1
    PBasic.BASIC_SPEC                   -- basicSpec1
    PBasic.FORMULA                      -- sentence1
    PBasic.SYMB_ITEMS                   -- symb_items1
    PBasic.SYMB_MAP_ITEMS               -- symb_map_items1
    PSign.Sign                          -- sign1
    PMor.Morphism                       -- morphism1
    PSymbol.Symbol                      -- symbol1
    PSymbol.Symbol                      -- raw_symbol1
    ()
    PLogic.Propositional                -- lid2
    PSL.PropSL                          -- sublogics2
    PBasic.BASIC_SPEC                   -- basicSpec2
    PBasic.FORMULA                      -- sentence2
    PBasic.SYMB_ITEMS                   -- symb_items2
    PBasic.SYMB_MAP_ITEMS               -- symb_map_items2
    PSign.Sign                          -- sign2
    PMor.Morphism                       -- morphism2
    PSymbol.Symbol                      -- symbol2
    PSymbol.Symbol                      -- raw_smybol2
    ()
    where
      sourceLogic Prop2CNF    = PLogic.Propositional
      sourceSublogic Prop2CNF = PSL.top
      targetLogic Prop2CNF    = PLogic.Propositional
      mapSublogic Prop2CNF    = mapSubProp2CNF
      map_symbol Prop2CNF     = mapSymbol
      map_morphism Prop2CNF   = mapMor
      map_theory Prop2CNF     = P2C.translateToCNF
      map_sentence Prop2CNF   = P2C.translateSentenceToCNF
      has_model_expansion Prop2CNF = True
      is_weakly_amalgamable Prop2CNF = True

-- | determination of target sublogic 
mapSubProp2CNF :: PSL.PropSL -> PSL.PropSL
mapSubProp2CNF sl 
    | PSL.isProp sl = PSL.PropSL
                        {
                          PSL.format    = PSL.CNF
                        }
    | PSL.isCNF sl = PSL.PropSL
                        {
                          PSL.format    = PSL.CNF
                        }
    | PSL.isHC sl  = PSL.PropSL
                        {
                          PSL.format    = PSL.HornClause
                        }
    | otherwise    = error "Impossible case"

-- | mapping of symbol... which is trivial in our case
mapSymbol :: PSymbol.Symbol -> Set.Set PSymbol.Symbol
mapSymbol sym = Set.singleton sym

-- | mapping of the signature
mapSig :: PSign.Sign -> PSign.Sign 
mapSig = id

-- | trivial map of morphisms
mapMor :: PMor.Morphism -> Result.Result PMor.Morphism
mapMor mor = Result.Result
             {
               Result.diags = []
             , Result.maybeResult = Just mor
             }
