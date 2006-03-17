{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  portable

Here is the place where the class Logic is instantiated for CASL.
   Also the instances for Syntax an Category.
-}

{- | todo:
  real implementation for map_sen
-}

module ConstraintCASL.Logic_ConstraintCASL(module ConstraintCASL.Logic_ConstraintCASL, CASLSign, ConstraintCASLMor) where

import Common.AS_Annotation
import Common.Result
import Common.Lexer((<<))
import Text.ParserCombinators.Parsec

import Logic.Logic

import ConstraintCASL.AS_ConstraintCASL
import ConstraintCASL.Parse_AS_Basic
import ConstraintCASL.Formula
import ConstraintCASL.StaticAna
import ConstraintCASL.ATC_ConstraintCASL()
import ConstraintCASL.Print_AS
import ConstraintCASL.LaTeX_AS

import CASL.AS_Basic_CASL
import CASL.LaTeX_CASL()
import CASL.SymbolParser
import CASL.MapSentence
import CASL.Amalgamability
import CASL.ATC_CASL()
import CASL.Sublogic
import CASL.Sign
import CASL.StaticAna
import CASL.Morphism
import CASL.SymbolMapAnalysis
import CASL.Taxonomy
import CASL.SimplifySen
import CASL.Logic_CASL
import CASL.CCC.FreeTypes
import CASL.CCC.OnePoint -- currently unused

data ConstraintCASL = ConstraintCASL deriving Show

instance Language ConstraintCASL where
 description _ =
  "ConstraintCASL - a restriction of CASL to constraint\ 
   \formulas over predicates"

-- dummy of "Min f e"
dummyMin :: b -> c -> Result ()
dummyMin _ _ = Result {diags = [], maybeResult = Just ()}

instance Category ConstraintCASL ConstraintCASLSign ConstraintCASLMor
    where
         -- ide :: id -> object -> morphism
         ide ConstraintCASL = idMor dummy
         -- comp :: id -> morphism -> morphism -> Maybe morphism
         comp ConstraintCASL = compose (const id)
         -- dom, cod :: id -> morphism -> object
         dom ConstraintCASL = msource
         cod ConstraintCASL = mtarget
         -- legal_obj :: id -> object -> Bool
         legal_obj ConstraintCASL = legalSign
         -- legal_mor :: id -> morphism -> Bool
         legal_mor ConstraintCASL = legalMor

-- abstract syntax, parsing (and printing)

instance Syntax ConstraintCASL ConstraintCASLBasicSpec
                SYMB_ITEMS SYMB_MAP_ITEMS
      where
         parse_basic_spec ConstraintCASL = Just $ basicSpec constraintKeywords
         parse_symb_items ConstraintCASL = Just $ symbItems []
         parse_symb_map_items ConstraintCASL = Just $ symbMapItems []

-- lattices (for sublogics)

{-instance LatticeWithTop CASL_Sublogics where
    -- meet, join :: l -> l -> l
    meet = CASL.Sublogic.sublogics_min
    join = CASL.Sublogic.sublogics_max
    -- top :: l
    top = CASL.Sublogic.top
-}
-- ConstraintCASL logic

instance Sentences ConstraintCASL ConstraintCASLFORMULA () ConstraintCASLSign ConstraintCASLMor Symbol where
      map_sen ConstraintCASL m = return . mapSen (\ _ -> id) m
      parse_sentence ConstraintCASL = Just (fmap item (aFormula [] << eof))
      sym_of ConstraintCASL = symOf
      symmap_of ConstraintCASL = morphismToSymbMap
      sym_name ConstraintCASL = symName
      conservativityCheck ConstraintCASL th mor phis = 
        error "conservativityCheck ConstraintCASL nyi"
      -- fmap (fmap fst) (checkFreeType th mor phis)
      simplify_sen ConstraintCASL = 
        error "simplify_sen ConstraintCASL nyi" -- simplifySen dummyMin dummy

instance StaticAnalysis ConstraintCASL ConstraintCASLBasicSpec ConstraintCASLFORMULA ()
               SYMB_ITEMS SYMB_MAP_ITEMS
               ConstraintCASLSign
               ConstraintCASLMor
               Symbol RawSymbol where
         basic_analysis ConstraintCASL = Just basicConstraintCASLAnalysis
         stat_symb_map_items ConstraintCASL = statSymbMapItems
         stat_symb_items ConstraintCASL = statSymbItems
         ensures_amalgamability ConstraintCASL (opts, diag, sink, desc) =
            error "ConstraintCASL.ensures_amalgamability not yet implemented"
             --ensuresAmalgamability opts diag sink desc

         sign_to_basic_spec ConstraintCASL _sigma _sens = Basic_spec [] -- ???

         symbol_to_raw ConstraintCASL = symbolToRaw
         id_to_raw ConstraintCASL = idToRaw
         matches ConstraintCASL = CASL.Morphism.matches
         is_transportable ConstraintCASL = isSortInjective

         empty_signature ConstraintCASL = emptySign ()
         signature_union ConstraintCASL sigma1 sigma2 =
           return $ addSig dummy sigma1 sigma2
         morphism_union ConstraintCASL = morphismUnion (const id) dummy
         final_union ConstraintCASL = finalUnion dummy
         is_subsig ConstraintCASL = isSubSig trueC
         inclusion ConstraintCASL = sigInclusion dummy trueC
         cogenerated_sign ConstraintCASL = cogeneratedSign dummy
         generated_sign ConstraintCASL = generatedSign dummy
         induced_from_morphism ConstraintCASL = inducedFromMorphism dummy
         induced_from_to_morphism ConstraintCASL = inducedFromToMorphism dummy trueC
         theory_to_taxonomy ConstraintCASL = 
           error "theory_to_taxonomy ConstraintCASL nyi" -- convTaxo


instance Logic ConstraintCASL CASL.Sublogic.CASL_Sublogics
               ConstraintCASLBasicSpec ConstraintCASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               ConstraintCASLSign
               ConstraintCASLMor
               Symbol RawSymbol () where

         stability _ = Experimental

         sublogic_names ConstraintCASL = CASL.Sublogic.sublogics_name
         all_sublogics ConstraintCASL = CASL.Sublogic.sublogics_all

         data_logic ConstraintCASL = Nothing

         is_in_basic_spec ConstraintCASL = CASL.Sublogic.in_basic_spec
         is_in_sentence ConstraintCASL = CASL.Sublogic.in_sentence
         is_in_symb_items ConstraintCASL = CASL.Sublogic.in_symb_items
         is_in_symb_map_items ConstraintCASL = CASL.Sublogic.in_symb_map_items
         is_in_sign ConstraintCASL = CASL.Sublogic.in_sign
         is_in_morphism ConstraintCASL = CASL.Sublogic.in_morphism
         is_in_symbol ConstraintCASL = CASL.Sublogic.in_symbol

         min_sublogic_basic_spec ConstraintCASL = CASL.Sublogic.sl_basic_spec
         min_sublogic_sentence ConstraintCASL = CASL.Sublogic.sl_sentence
         min_sublogic_symb_items ConstraintCASL = CASL.Sublogic.sl_symb_items
         min_sublogic_symb_map_items ConstraintCASL = CASL.Sublogic.sl_symb_map_items
         min_sublogic_sign ConstraintCASL = CASL.Sublogic.sl_sign
         min_sublogic_morphism ConstraintCASL = CASL.Sublogic.sl_morphism
         min_sublogic_symbol ConstraintCASL = CASL.Sublogic.sl_symbol

         proj_sublogic_basic_spec ConstraintCASL = CASL.Sublogic.pr_basic_spec
         proj_sublogic_symb_items ConstraintCASL = CASL.Sublogic.pr_symb_items
         proj_sublogic_symb_map_items ConstraintCASL = CASL.Sublogic.pr_symb_map_items
         proj_sublogic_sign ConstraintCASL = CASL.Sublogic.pr_sign
         proj_sublogic_morphism ConstraintCASL = CASL.Sublogic.pr_morphism
         proj_sublogic_epsilon ConstraintCASL = CASL.Sublogic.pr_epsilon dummy
         proj_sublogic_symbol ConstraintCASL = CASL.Sublogic.pr_symbol
