{-# LANGUAGE MultiParamTypeClasses #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for propositional logic
               extended with QBFs

Copyright   :  (c) Jonathan von Schroeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  jonathan.von_schroeder@dfki.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Instance of class Logic for the propositional logic extended with QBFs
   Also the instances for Syntax and Category.

  Ref.

  <http://en.wikipedia.org/wiki/Propositional_logic>

  Till Mossakowski, Joseph Goguen, Razvan Diaconescu, Andrzej Tarlecki.
  What is a Logic?.
  In Jean-Yves Beziau (Ed.), Logica Universalis, pp. 113-133. Birkhaeuser.
  2005.

  <http://www.voronkov.com/lics.cgi>
-}

module QBF.Logic_QBF where

import Logic.Logic

import Propositional.Sign
import QBF.Morphism
import QBF.AS_BASIC_QBF
import QBF.ATC_QBF ()
import QBF.Symbol as Symbol
import QBF.Parse_AS_Basic
import QBF.Analysis
import QBF.Sublogic as Sublogic
import QBF.Tools

import ATC.ProofTree ()
import Common.ProofTree

import Common.ProverTools
import QBF.ProveDepQBF

import qualified Data.Map as Map

-- | Lid for propositional logic
data QBF = QBF deriving Show

instance Language QBF where
    description _ = "Propositional Logic extended with QBFs\n"
        ++ "for more information please refer to\n"
        ++ "http://en.wikipedia.org/wiki/Propositional_logic"
        ++ "http://www.voronkov.com/lics.cgi"

-- | Instance of Category for propositional logic
instance Category Sign Morphism where
    -- Identity morhpism
    ide = idMor
    -- Returns the domain of a morphism
    dom = source
    -- Returns the codomain of a morphism
    cod = target
    -- check if morphism is inclusion
    isInclusion = Map.null . propMap
    -- tests if the morphism is ok
    legal_mor = isLegalMorphism
    -- composition of morphisms
    composeMorphisms = composeMor

-- | Instance of Sentences for propositional logic
instance Sentences QBF FORMULA
    Sign Morphism Symbol where
    negation QBF = Just . negateFormula
    -- returns the set of symbols
    sym_of QBF = singletonList . symOf
    -- returns the symbol map
    symmap_of QBF = getSymbolMap
    -- returns the name of a symbol
    sym_name QBF = getSymbolName
    -- translation of sentences along signature morphism
    map_sen QBF = mapSentence
    -- there is nothing to leave out
    simplify_sen QBF _ = simplify

-- | Syntax of Propositional logic
instance Syntax QBF BASICSPEC
    SYMBITEMS SYMBMAPITEMS where
         parse_basic_spec QBF = Just basicSpec
         parse_symb_items QBF = Just symbItems
         parse_symb_map_items QBF = Just symbMapItems

-- | Instance of Logic for propositional logc
instance Logic QBF
    QBFSL                     -- Sublogics
    BASICSPEC                 -- basic_spec
    FORMULA                   -- sentence
    SYMBITEMS                 -- symb_items
    SYMBMAPITEMS              -- symb_map_items
    Sign                      -- sign
    Morphism                  -- morphism
    Symbol                    -- symbol
    Symbol                    -- raw_symbol
    ProofTree                 -- proof_tree
    where
      stability QBF = Experimental
      top_sublogic QBF = Sublogic.top
      all_sublogics QBF = sublogicsAll
      empty_proof_tree QBF = emptyProofTree
    -- supplied provers
      provers QBF = []
        ++ unsafeProverCheck "depqbf" "PATH" depQBFProver

-- | Static Analysis for propositional logic
instance StaticAnalysis QBF
    BASICSPEC                 -- basic_spec
    FORMULA                   -- sentence
    SYMBITEMS                 -- symb_items
    SYMBMAPITEMS              -- symb_map_items
    Sign                      -- sign
    Morphism                  -- morphism
    Symbol                    -- symbol
    Symbol                    -- raw_symbol
        where
          basic_analysis QBF =
              Just basicPropositionalAnalysis
          empty_signature QBF = emptySig
          is_subsig QBF = isSubSigOf
          subsig_inclusion QBF s = return . inclusionMap s
          signature_union QBF = sigUnion
          symbol_to_raw QBF = symbolToRaw
          id_to_raw QBF = idToRaw
          matches QBF = Symbol.matches
          stat_symb_items QBF = mkStatSymbItems
          stat_symb_map_items QBF = mkStatSymbMapItem
          morphism_union QBF = morphismUnion
          induced_from_morphism QBF = inducedFromMorphism
          induced_from_to_morphism QBF = inducedFromToMorphism
          signature_colimit QBF = signatureColimit

-- | Sublogics
instance SemiLatticeWithTop QBFSL where
    join = sublogicsMax
    top = Sublogic.top

instance MinSublogic QBFSL BASICSPEC where
     minSublogic = slBasicSpec bottom

instance MinSublogic QBFSL Sign where
    minSublogic = slSig bottom

instance SublogicName QBFSL where
    sublogicName = sublogicsName

instance MinSublogic QBFSL FORMULA where
    minSublogic = slForm bottom

instance MinSublogic QBFSL Symbol where
    minSublogic = slSym bottom

instance MinSublogic QBFSL SYMBITEMS where
    minSublogic = slSymit bottom

instance MinSublogic QBFSL Morphism where
    minSublogic = slMor bottom

instance MinSublogic QBFSL SYMBMAPITEMS where
    minSublogic = slSymmap bottom

instance ProjectSublogicM QBFSL Symbol where
    projectSublogicM = prSymbolM

instance ProjectSublogic QBFSL Sign where
    projectSublogic = prSig

instance ProjectSublogic QBFSL Morphism where
    projectSublogic = prMor

instance ProjectSublogicM QBFSL SYMBMAPITEMS where
    projectSublogicM = prSymMapM

instance ProjectSublogicM QBFSL SYMBITEMS where
    projectSublogicM = prSymM

instance ProjectSublogic QBFSL BASICSPEC where
    projectSublogic = prBasicSpec

instance ProjectSublogicM QBFSL FORMULA where
    projectSublogicM = prFormulaM
