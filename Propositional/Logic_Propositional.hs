{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Instance of class Logic for the propositional logic
   Also the instances for Syntax and Category.
-}

{-
  Ref.

  http://en.wikipedia.org/wiki/Propositional_logic

  Till Mossakowski, Joseph Goguen, Razvan Diaconescu, Andrzej Tarlecki.
  What is a Logic?.
  In Jean-Yves Beziau (Ed.), Logica Universalis, pp. 113-@133. Birkhaeuser.
  2005.
-}

module Propositional.Logic_Propositional
    (module Propositional.Logic_Propositional
            , Sign
            , Morphism
    ) where

import Common.ProofTree

import ATC.ProofTree ()

import Logic.Logic

import Propositional.Sign as Sign
import Propositional.Morphism as Morphism
import qualified Propositional.AS_BASIC_Propositional as AS_BASIC
import qualified Propositional.ATC_Propositional()
import qualified Propositional.Symbol as Symbol
import qualified Propositional.Parse_AS_Basic as Parse_AS
import qualified Propositional.Analysis as Analysis
import qualified Propositional.Sublogic as Sublogic

#ifdef UNI_PACKAGE
#ifdef TABULAR_PACKAGE
import qualified Propositional.ProveWithTruthTable as ProveTT
#endif
import qualified Propositional.Prove as Prove
import Propositional.Conservativity
#endif

-- | Lid for propositional logic
data Propositional = Propositional deriving Show --lid

instance Language Propositional where
    description _ =
        "Propositional Logic\n"++
         "for more information please refer to\n"++
         "http://en.wikipedia.org/wiki/Propositional_logic"


-- | Instance of Category for propositional logic
instance Category Sign.Sign Morphism.Morphism where
    -- Identity morhpism
    ide = Morphism.idMor
    -- Returns the domain of a morphism
    dom = Morphism.source
    -- Returns the codomain of a morphism
    cod = Morphism.target
    -- tests if the morphism is ok
    legal_mor f = Morphism.isLegalMorphism f
    -- composition of morphisms
    comp f g = Morphism.composeMor f g

-- | Instance of Sentences for propositional logic
instance Sentences Propositional AS_BASIC.FORMULA
    Sign.Sign Morphism.Morphism Symbol.Symbol where
    -- returns the set of symbols
    sym_of Propositional = Symbol.symOf
    -- returns the symbol map
    symmap_of Propositional = Symbol.getSymbolMap
    -- returns the name of a symbol
    sym_name Propositional = Symbol.getSymbolName
    -- translation of sentences along signature morphism
    map_sen Propositional = Morphism.mapSentence
    -- there is nothing to leave out
    simplify_sen Propositional _ form = form

-- | Syntax of Propositional logic
instance Syntax Propositional AS_BASIC.BASIC_SPEC
    AS_BASIC.SYMB_ITEMS AS_BASIC.SYMB_MAP_ITEMS where
         parse_basic_spec Propositional = Just Parse_AS.basicSpec
         parse_symb_items _ = Nothing
         parse_symb_map_items _ = Nothing

-- | Instance of Logic for propositional logc
instance Logic Propositional
    Sublogic.PropSL                    -- Sublogics
    AS_BASIC.BASIC_SPEC                -- basic_spec
    AS_BASIC.FORMULA                   -- sentence
    AS_BASIC.SYMB_ITEMS                -- symb_items
    AS_BASIC.SYMB_MAP_ITEMS            -- symb_map_items
    Sign.Sign                          -- sign
    Morphism.Morphism                  -- morphism
    Symbol.Symbol                      -- symbol
    Symbol.Symbol                      -- raw_symbol
    ProofTree                      -- proof_tree
    where
      stability Propositional     = Experimental
      top_sublogic Propositional  = Sublogic.top
      all_sublogics Propositional = Sublogic.sublogics_all
    -- supplied provers
#ifdef UNI_PACKAGE
      provers Propositional = [Prove.zchaffProver
#ifdef TABULAR_PACKAGE
                              ,ProveTT.ttProver
#endif
                              ]
      cons_checkers Propositional = 
         [Prove.propConsChecker,ProveTT.ttConsistencyChecker]
      conservativityCheck Propositional = conserChose
#endif


-- | Static Analysis for propositional logic
instance StaticAnalysis Propositional
    AS_BASIC.BASIC_SPEC                -- basic_spec
    AS_BASIC.FORMULA                   -- sentence
    AS_BASIC.SYMB_ITEMS                -- symb_items
    AS_BASIC.SYMB_MAP_ITEMS            -- symb_map_items
    Sign.Sign                          -- sign
    Morphism.Morphism                  -- morphism
    Symbol.Symbol                      -- symbol
    Symbol.Symbol                      -- raw_symbol
        where
          basic_analysis Propositional           =
              Just $ Analysis.basicPropositionalAnalysis
          empty_signature Propositional          = Sign.emptySig
          inclusion Propositional                = Morphism.inclusionMap
          signature_union Propositional          = Sign.sigUnion
          symbol_to_raw Propositional            = Symbol.symbolToRaw
          id_to_raw     Propositional            = Symbol.idToRaw
          matches       Propositional            = Symbol.matches
          stat_symb_items Propositional          = Analysis.mkStatSymbItems
          stat_symb_map_items Propositional      = Analysis.mkStatSymbMapItem
          induced_from_morphism Propositional    = Analysis.inducedFromMorphism
          induced_from_to_morphism Propositional =
              Analysis.inducedFromToMorphism
          signature_colimit Propositional  = Analysis.signatureColimit

-- | Sublogics
instance SemiLatticeWithTop Sublogic.PropSL where
    join = Sublogic.sublogics_max
    top  = Sublogic.top

instance MinSublogic Sublogic.PropSL AS_BASIC.BASIC_SPEC where
     minSublogic it = Sublogic.sl_basic_spec Sublogic.bottom it

instance MinSublogic Sublogic.PropSL Sign.Sign where
    minSublogic si = Sublogic.sl_sig Sublogic.bottom si

instance SublogicName Sublogic.PropSL where
    sublogicName = Sublogic.sublogics_name

instance MinSublogic Sublogic.PropSL AS_BASIC.FORMULA where
    minSublogic frm = Sublogic.sl_form Sublogic.bottom frm

instance MinSublogic Sublogic.PropSL Symbol.Symbol where
    minSublogic sym = Sublogic.sl_sym Sublogic.bottom sym

instance MinSublogic Sublogic.PropSL AS_BASIC.SYMB_ITEMS where
    minSublogic symit = Sublogic.sl_symit Sublogic.bottom symit

instance MinSublogic Sublogic.PropSL Morphism.Morphism where
    minSublogic symor = Sublogic.sl_mor Sublogic.bottom symor

instance MinSublogic Sublogic.PropSL AS_BASIC.SYMB_MAP_ITEMS where
    minSublogic sm = Sublogic.sl_symmap Sublogic.bottom sm

instance ProjectSublogicM Sublogic.PropSL Symbol.Symbol where
    projectSublogicM = Sublogic.prSymbolM

instance ProjectSublogic Sublogic.PropSL Sign.Sign where
    projectSublogic = Sublogic.prSig

instance ProjectSublogic Sublogic.PropSL Morphism.Morphism where
    projectSublogic = Sublogic.prMor

instance ProjectSublogicM Sublogic.PropSL AS_BASIC.SYMB_MAP_ITEMS where
    projectSublogicM = Sublogic.prSymMapM

instance ProjectSublogicM Sublogic.PropSL AS_BASIC.SYMB_ITEMS where
    projectSublogicM = Sublogic.prSymM

instance ProjectSublogic Sublogic.PropSL AS_BASIC.BASIC_SPEC where
    projectSublogic = Sublogic.prBasicSpec

instance ProjectSublogicM Sublogic.PropSL AS_BASIC.FORMULA where
    projectSublogicM = Sublogic.prFormulaM
