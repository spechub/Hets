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

module Temporal.Logic_Temporal
    (module Temporal.Logic_Temporal
            , Sign
            , Morphism
    ) where

import Common.ProofTree
import Common.Consistency

import ATC.ProofTree ()

import Logic.Logic

import Propositional.Sign as Sign
import Propositional.Morphism as Morphism
import qualified Propositional.AS_BASIC_Propositional as AS_BASIC
import qualified Propositional.ATC_Propositional()
import qualified Propositional.Symbol as Symbol
import qualified Propositional.Parse_AS_Basic as Parse_AS
import qualified Propositional.Analysis as Analysis


-- | Lid for propositional logic
data Temproal = Temporal deriving Show --lid

instance Language Temporal where
    description _ =
        "Temporal Logic\n"++
         "for more information please refer to\n"++
         "http://en.wikipedia.org/wiki/Temporal_logic"


-- beibehalten
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

-- Symbol von Propositional uebernehmen
-- | Instance of Sentences for propositional logic
instance Sentences Temporal (StateFormula Id)
    Sign.Sign Morphism.Morphism Symbol.Symbol where
    -- returns the set of symbols
    sym_of Temporal = Symbol.symOf
    -- returns the symbol map
    symmap_of Temporal = Symbol.getSymbolMap
    -- returns the name of a symbol
    sym_name Temporal = Symbol.getSymbolName
    -- translation of sentences along signature morphism
    map_sen Temporal = Morphism.mapSentence
    -- there is nothing to leave out
    simplify_sen Temporal _ form = form

-- BASIC_SPEC: von Propositional uebernehmen (abstrakte Syntax)
-- aber Formeln neu machen
-- | Syntax of Temporal logic
instance Syntax Temporal AS_BASIC.BASIC_SPEC () () where
         -- hier den Parser einbinden
         parse_basic_spec Temporal = Just Parse_AS.basicSpec
         parse_symb_items _ = Nothing
         parse_symb_map_items _ = Nothing

-- | Instance of Logic for propositional logc
instance Logic Temporal
      -- erstmal (), spaeter Datentyp fuer Sublogiken
    Sublogic.PropSL                    -- Sublogics 
    AS_BASIC.BASIC_SPEC                -- basic_spec
    AS_BASIC.FORMULA                   -- sentence
    ()                -- symb_items
    ()            -- symb_map_items
    Sign.Sign                          -- sign
    Morphism.Morphism                  -- morphism
    Symbol.Symbol                      -- symbol
    Symbol.Symbol                      -- raw_symbol
    ()                      -- proof_tree
    where
      stability Temporal     = Experimental
      top_sublogic Temporal  = ()
      all_sublogics Temporal = ()
    -- supplied provers
      provers Temporal = []  -- spaeter: nuSMV
      cons_checkers Temporal = []
      conservativityCheck Temporal = []


-- groﬂteils uebernehmen
-- | Static Analysis for propositional logic
instance StaticAnalysis Temporal
    AS_BASIC.BASIC_SPEC                -- basic_spec
    AS_BASIC.FORMULA                   -- sentence
    AS_BASIC.SYMB_ITEMS                -- symb_items
    AS_BASIC.SYMB_MAP_ITEMS            -- symb_map_items
    Sign.Sign                          -- sign
    Morphism.Morphism                  -- morphism
    Symbol.Symbol                      -- symbol
    Symbol.Symbol                      -- raw_symbol
        where
          basic_analysis Temporal           =
              Just $ Analysis.basicTemporalAnalysis
          empty_signature Temporal          = Sign.emptySig
          inclusion Temporal                = Morphism.inclusionMap
          signature_union Temporal          = Sign.sigUnion
          symbol_to_raw Temporal            = Symbol.symbolToRaw
          id_to_raw     Temporal            = Symbol.idToRaw
          matches       Temporal            = Symbol.matches
          stat_symb_items Temporal          = Analysis.mkStatSymbItems
          stat_symb_map_items Temporal      = Analysis.mkStatSymbMapItem
          induced_from_morphism Temporal    = Analysis.inducedFromMorphism
          induced_from_to_morphism Temporal =
              Analysis.inducedFromToMorphism
          signature_colimit Temporal  = Analysis.signatureColimit

-- | Sublogics
instance SemiLatticeWithTop Sublogic.PropSL where
    join _ _ = ()
    top  = ()

-- alles durch Rueckgabewert () ersetzen
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
