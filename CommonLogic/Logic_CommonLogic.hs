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

module CommonLogic.Logic_CommonLogic where

import Logic.Logic


import ATC.ProofTree ()
import Common.ProofTree
import Common.DefaultMorphism

import CommonLogic.AS_CommonLogic

-- | Lid for propositional logic
data CommonLogic = CommonLogic deriving Show

instance Language CommonLogic where
    description _ = "CommonLogic Logic\n"
        ++ "for more information please refer to\n"
        ++ "http://en.wikipedia.org/wiki/Propositional_logic"

data Sign = Sign
-- | Instance of Category derived by default

{-
-- | Instance of Sentences for propositional logic
instance Sentences CommonLogic SENTENCE Sign (DefaultMorphism Sign) ()
{-
  where
    negation CommonLogic = Just . negateFormula
    -- returns the set of symbols
    sym_of CommonLogic = symOf
    -- returns the symbol map
    symmap_of CommonLogic = getSymbolMap
    -- returns the name of a symbol
    sym_name CommonLogic = getSymbolName
    -- translation of sentences along signature morphism
    map_sen CommonLogic = mapSentence
    -- there is nothing to leave out
    simplify_sen CommonLogic _ = simplify
-}

-- | Syntax of CommonLogic logic
instance Syntax CommonLogic [SENTENCE] () ()
{-
         parse_basic_spec CommonLogic = Just basicSpec
         parse_symb_items CommonLogic = Just symbItems
         parse_symb_map_items CommonLogic = Just symbMapItems
-}

-- | Instance of Logic for propositional logc
instance Logic CommonLogic
    ()                    -- Sublogics
    [SENTENCE]                -- basic_spec
    SENTENCE                   -- sentence
    ()                -- symb_items
    ()            -- symb_map_items
    Sign                          -- sign
    (DefaultMorphism Sign)                 -- morphism
    ()                      -- symbol
    ()                      -- raw_symbol
    ()                     -- proof_tree

-- | Static Analysis for propositional logic
instance StaticAnalysis CommonLogic
    [SENTENCE]               -- basic_spec
    SENTENCE                   -- sentence
    ()
    ()
    Sign                          -- sign
    (DefaultMorphism Sign)
    ()
    ()
{-
        where
          basic_analysis CommonLogic           =
              Just basicCommonLogicAnalysis
          empty_signature CommonLogic          = emptySig
          is_subsig CommonLogic                = isSubSigOf
          subsig_inclusion CommonLogic s = return . inclusionMap s
          signature_union CommonLogic          = sigUnion
          symbol_to_raw CommonLogic            = symbolToRaw
          id_to_raw     CommonLogic            = idToRaw
          matches       CommonLogic            = Symbol.matches
          stat_symb_items CommonLogic          = mkStatSymbItems
          stat_symb_map_items CommonLogic      = mkStatSymbMapItem
          morphism_union CommonLogic           = morphismUnion
          induced_from_morphism CommonLogic    = inducedFromMorphism
          induced_from_to_morphism CommonLogic = inducedFromToMorphism
          signature_colimit CommonLogic  = signatureColimit
-}
-}
