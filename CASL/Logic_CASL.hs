
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

import CASL.Sublogic
import CASL.StaticAna
import CASL.Morphism

-- a dummy datatype for the LogicGraph and for identifying the right
-- instances
data CASL = CASL deriving (Show)
instance Language CASL  -- default definition is okay

instance Category CASL Sign Morphism  
    where
         -- ide :: id -> object -> morphism
	 ide CASL sigma = Morphism { msource = sigma,
                                     mtarget = sigma,
				     sort_map = empty,
				     fun_map = empty,
				     pred_map = empty
                                   }
         -- o :: id -> morphism -> morphism -> Maybe morphism
	 comp CASL sigma1 _sigma2 = Just sigma1 -- ???
         -- dom, cod :: id -> morphism -> object
	 dom CASL _ = emptySign
	 cod CASL _ = emptySign
         -- legal_obj :: id -> object -> Bool
	 legal_obj CASL _ = fun_err "legall_obj"
         -- legal_mor :: id -> morphism -> Bool
	 legal_mor CASL _ = fun_err "legal_mor"


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

instance Sentences CASL Sentence () Sign Morphism Symbol where
      map_sen CASL _morphism s = return s
      parse_sentence CASL _sign str = 
	  case runParser (aFormula << eof) emptyAnnos "" str of
	  Right x -> return $ item x
	  Left err -> fail $ show err
      provers CASL = [] 
      cons_checkers CASL = []

instance StaticAnalysis CASL BASIC_SPEC Sentence ()
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
	 ensures_amalgamability CASL _ = fail "ensures_amalgamability nyi"

         sign_to_basic_spec CASL _sigma _sens = Basic_spec []

         symbol_to_raw CASL = symbolToRaw
         id_to_raw CASL = idToRaw
         sym_of CASL = symOf
         symmap_of CASL = symmapOf
         matches CASL = CASL.Morphism.matches
         sym_name CASL = symName
         
         -- add_sign :: id -> Sign -> Sign -> Sign
	 add_sign CASL = addSig
         empty_signature CASL = emptySign
         signature_union CASL sigma1 _sigma2 = return sigma1 -- ??? incorrect
         morphism_union CASL mor1 _mor2 = return mor1 -- ??? incorrect
         -- final_union :: id -> Sign -> Sign -> Result Sign
	 final_union CASL s1 s2 = return $ addSig s1 s2
         is_subsig CASL = isSubSig
         cogenerated_sign CASL _rsys sigma = return (ide CASL sigma)
         generated_sign CASL _rsys sigma = return (ide CASL sigma)
         -- generated_sign, cogenerated_sign :: id -> [RawSymbol]
         --                -> Sign -> Result Morphism
         induced_from_morphism CASL _rmap sigma = return (ide CASL sigma)-- ???
         induced_from_to_morphism CASL _rmap sigmaS _sigmaT =
           return (ide CASL sigmaS) -- ???
         --induced_from_to_morphism :: id -> EndoMap RawSymbol
         --               -> Sign -> Sign -> Result Morphism
         -- extend_morphism :: id -> Sign -> Morphism -> Sign -> Sign
         --               -> Result Morphism
         extend_morphism CASL _s m _s1 _s2 = return m

instance Logic CASL CASL.Sublogic.CASL_Sublogics
               BASIC_SPEC Sentence SYMB_ITEMS SYMB_MAP_ITEMS
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
