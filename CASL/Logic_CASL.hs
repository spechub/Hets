
{- HetCATS/CASL/Logic_CASL.hs
   $Id$
   Authors: Klaus Lüttich
   Year:    2002

   Here is the place where the class Logic is instantiated for CASL.
   Also the instances for Syntax an Category.

   todo:
     - writing real functions

-}

module CASL.Logic_CASL where

import CASL.AS_Basic_CASL
import CASL.Print_AS_Basic
import CASL.Parse_AS_Basic
import CASL.SymbolParser
import Logic.ParsecInterface
import Common.AS_Annotation
import Common.AnnoState(emptyAnnos)
import Common.Lib.Parsec
import Common.Lib.Map
import Logic.Logic
import Common.Lexer((<<))
import Common.Result
import Common.Id
import CASL.ATC_CASL

import CASL.Sublogic
import CASL.Sign
import CASL.StaticAna
import CASL.Morphism
import CASL.SymbolMapAnalysis

-- a dummy datatype for the LogicGraph and for identifying the right
-- instances
data CASL = CASL deriving (Show)
instance Language CASL  -- default definition is okay

instance Category CASL Sign Morphism  
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

instance Syntax CASL BASIC_SPEC 
		SYMB_ITEMS SYMB_MAP_ITEMS
      where 
         parse_basic_spec CASL = Just(toParseFun basicSpec emptyAnnos)
	 parse_symb_items CASL = Just(toParseFun symbItems ())
	 parse_symb_map_items CASL = Just(toParseFun symbMapItems ())

-- lattices (for sublogics)

instance LatticeWithTop CASL_Sublogics where
    -- meet, join :: l -> l -> l
    meet = CASL.Sublogic.sublogics_min
    join = CASL.Sublogic.sublogics_max
    -- top :: l
    top = CASL.Sublogic.top

-- CASL logic

instance Sentences CASL FORMULA () Sign Morphism Symbol where
      map_sen CASL _morphism s = return s -- ???
      parse_sentence CASL _sign str = 
	  case runParser (aFormula << eof) emptyAnnos "" str of
	  Right x -> return $ item x
	  Left err -> fail $ show err
      provers CASL = [] 
      cons_checkers CASL = []

instance StaticAnalysis CASL BASIC_SPEC FORMULA ()
               SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               Morphism 
               Symbol RawSymbol where
         basic_analysis CASL = Just basicAnalysis
         stat_symb_map_items CASL = statSymbMapItems
         stat_symb_items CASL = statSymbItems
         -- ensures_amalgamability :: id
         --   -> (Diagram Sign Morphism, Node, Sign, LEdge Morphism, Morphism)
         --   -> Result (Diagram Sign Morphism)
	 ensures_amalgamability CASL _ = fail "ensures_amalgamability nyi" -- ???

         sign_to_basic_spec CASL _sigma _sens = Basic_spec [] -- ???

         symbol_to_raw CASL = symbolToRaw
         id_to_raw CASL = idToRaw
         sym_of CASL = symOf
         symmap_of CASL = morphismToSymbMap
         matches CASL = CASL.Morphism.matches
         sym_name CASL = symName
         
         empty_signature CASL = emptySign
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
               BASIC_SPEC FORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               Sign 
               Morphism
               Symbol RawSymbol () where
         sublogic_names CASL = CASL.Sublogic.sublogics_name
         all_sublogics CASL = CASL.Sublogic.sublogics_all

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

---- helpers ---------------------------------
fun_err :: String -> a
fun_err fname = 
    error ("*** Function \"" ++ fname ++ "\" is not yet implemented!")

----------------------------------------------
