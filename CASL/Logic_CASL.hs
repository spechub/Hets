{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Here is the place where the class Logic is instantiated for CASL.
   Also the instances for Syntax an Category.
-}

module CASL.Logic_CASL(CASL(CASL), CASLFORMULA, CASLSign, CASLMor, 
		       CASLBasicSpec) where

import CASL.AS_Basic_CASL
import CASL.LaTeX_CASL
import CASL.Parse_AS_Basic
import CASL.SymbolParser
import CASL.MapSentence
import Common.AS_Annotation
import Common.AnnoState(emptyAnnos)
import Common.Lib.Parsec
import Logic.Logic
import Common.Lexer((<<))
import CASL.ATC_CASL

import CASL.Sublogic
import CASL.Sign
import CASL.StaticAna
import CASL.Morphism
import CASL.SymbolMapAnalysis

data CASL = CASL deriving Show

instance Language CASL  -- default definition is okay

type CASLBasicSpec = BASIC_SPEC () () ()
type CASLSign = Sign () ()
type CASLMor = Morphism () () ()
type CASLFORMULA = FORMULA ()

instance Category CASL CASLSign CASLMor  
    where
         -- ide :: id -> object -> morphism
	 ide CASL = idMor
         -- comp :: id -> morphism -> morphism -> Maybe morphism
	 comp CASL = compose
         -- dom, cod :: id -> morphism -> object
	 dom CASL = msource
	 cod CASL = mtarget
         -- legal_obj :: id -> object -> Bool
	 legal_obj CASL = legalSign
         -- legal_mor :: id -> morphism -> Bool
	 legal_mor CASL = legalMor


-- abstract syntax, parsing (and printing)

instance Syntax CASL CASLBasicSpec
		SYMB_ITEMS SYMB_MAP_ITEMS
      where 
         parse_basic_spec CASL = Just basicSpec
	 parse_symb_items CASL = Just symbItems
	 parse_symb_map_items CASL = Just symbMapItems

-- lattices (for sublogics)

instance LatticeWithTop CASL_Sublogics where
    -- meet, join :: l -> l -> l
    meet = CASL.Sublogic.sublogics_min
    join = CASL.Sublogic.sublogics_max
    -- top :: l
    top = CASL.Sublogic.top

-- CASL logic

instance Sentences CASL CASLFORMULA () CASLSign CASLMor Symbol where
      map_sen CASL = mapSen
      parse_sentence CASL = Just
        ( \ _sign str ->
	  case runParser (aFormula << eof) emptyAnnos "" str of
	  Right x -> return $ item x
	  Left err -> fail $ show err )
      sym_of CASL = symOf
      symmap_of CASL = morphismToSymbMap
      sym_name CASL = symName
      provers CASL = [] 
      cons_checkers CASL = []

instance StaticAnalysis CASL CASLBasicSpec CASLFORMULA ()
               SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign 
               CASLMor 
               Symbol RawSymbol where
         basic_analysis CASL = Just $ basicAnalysis 
			       (const id) (const id) return
         stat_symb_map_items CASL = statSymbMapItems
         stat_symb_items CASL = statSymbItems
         -- ensures_amalgamability :: id
         --   -> (Diagram CASLSign CASLMor, Node, CASLSign, LEdge CASLMor, CASLMor)
         --   -> Result (Diagram CASLSign CASLMor)
	 ensures_amalgamability CASL _ = fail "ensures_amalgamability nyi" -- ???

         sign_to_basic_spec CASL _sigma _sens = Basic_spec [] -- ???

         symbol_to_raw CASL = symbolToRaw
         id_to_raw CASL = idToRaw
         matches CASL = CASL.Morphism.matches
         
         empty_signature CASL = emptySign ()
         signature_union CASL sigma1 sigma2 = 
           return $ addSig sigma1 sigma2
         morphism_union CASL = morphismUnion
	 final_union CASL = finalUnion
         is_subsig CASL = isSubSig
         inclusion CASL = sigInclusion
         cogenerated_sign CASL = cogeneratedSign
         generated_sign CASL = generatedSign
         induced_from_morphism CASL = inducedFromMorphism
         induced_from_to_morphism CASL = inducedFromToMorphism

instance Logic CASL CASL.Sublogic.CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign 
               CASLMor
               Symbol RawSymbol () where
         sublogic_names CASL = CASL.Sublogic.sublogics_name
         all_sublogics CASL = CASL.Sublogic.sublogics_all

         data_logic CASL = Nothing

         is_in_basic_spec CASL = CASL.Sublogic.in_basic_spec
         is_in_sentence CASL = CASL.Sublogic.in_sentence
         is_in_symb_items CASL = CASL.Sublogic.in_symb_items
         is_in_symb_map_items CASL = CASL.Sublogic.in_symb_map_items
         is_in_sign CASL = CASL.Sublogic.in_sign
         is_in_morphism CASL = CASL.Sublogic.in_morphism
         is_in_symbol CASL = CASL.Sublogic.in_symbol

         min_sublogic_basic_spec CASL = CASL.Sublogic.sl_basic_spec
         min_sublogic_sentence CASL = CASL.Sublogic.sl_sentence
         min_sublogic_symb_items CASL = CASL.Sublogic.sl_symb_items
         min_sublogic_symb_map_items CASL = CASL.Sublogic.sl_symb_map_items
         min_sublogic_sign CASL = CASL.Sublogic.sl_sign
         min_sublogic_morphism CASL = CASL.Sublogic.sl_morphism
         min_sublogic_symbol CASL = CASL.Sublogic.sl_symbol

         proj_sublogic_basic_spec CASL = CASL.Sublogic.pr_basic_spec
         proj_sublogic_symb_items CASL = CASL.Sublogic.pr_symb_items
         proj_sublogic_symb_map_items CASL = CASL.Sublogic.pr_symb_map_items
         proj_sublogic_sign CASL = CASL.Sublogic.pr_sign
         proj_sublogic_morphism CASL = CASL.Sublogic.pr_morphism
         proj_sublogic_epsilon CASL = CASL.Sublogic.pr_epsilon
         proj_sublogic_symbol CASL = CASL.Sublogic.pr_symbol
