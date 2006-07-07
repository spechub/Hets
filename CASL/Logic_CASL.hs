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

module CASL.Logic_CASL(module CASL.Logic_CASL, CASLSign, CASLMor) where

import Common.AS_Annotation
import Common.Result
import Common.Lexer((<<))
import Text.ParserCombinators.Parsec

import Logic.Logic

import CASL.AS_Basic_CASL
import CASL.Parse_AS_Basic
import CASL.ToDoc
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
import CASL.CCC.FreeTypes
import CASL.CCC.OnePoint -- currently unused

data CASL = CASL deriving Show

instance Language CASL where
 description _ =
  "CASL - the Common algebraic specification language\n\
  \This logic is subsorted partial first-order logic \
  \with sort generation constraints\n\
  \See the CASL User Manual, LNCS 2900, Springer Verlag\n\
  \and the CASL Reference Manual, LNCS 2960, Springer Verlag\n\
  \See also http://www.cofi.info/CASL.html"

type CASLBasicSpec = BASIC_SPEC () () ()
type CASLFORMULA = FORMULA ()
-- Following types are imported from CASL.Amalgamability:
-- type CASLSign = Sign () ()
-- type CASLMor = Morphism () () ()

dummy :: a -> b -> ()
dummy _ _ = ()

-- dummy of "Min f e"
dummyMin :: b -> c -> Result ()
dummyMin _ _ = Result {diags = [], maybeResult = Just ()}

trueC :: a -> b -> Bool
trueC _ _ = True

instance Category CASL CASLSign CASLMor
    where
         -- ide :: id -> object -> morphism
         ide CASL = idMor dummy
         -- comp :: id -> morphism -> morphism -> Maybe morphism
         comp CASL = compose (const id)
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
         parse_basic_spec CASL = Just $ basicSpec []
         parse_symb_items CASL = Just $ symbItems []
         parse_symb_map_items CASL = Just $ symbMapItems []

-- lattices (for sublogics)

instance SemiLatticeWithTop CASL_Sublogics where
    join = CASL.Sublogic.sublogics_max
    top = CASL.Sublogic.top

-- CASL logic

instance Sentences CASL CASLFORMULA () CASLSign CASLMor Symbol where
      map_sen CASL m = return . mapSen (\ _ -> id) m
      parse_sentence CASL = Just (fmap item (aFormula [] << eof))
      sym_of CASL = symOf
      symmap_of CASL = morphismToSymbMap
      sym_name CASL = symName
      conservativityCheck CASL th mor phis = 
          fmap (fmap fst) (checkFreeType th mor phis)
      simplify_sen CASL = simplifySen dummyMin dummy
      print_named CASL = printTheoryFormula

instance StaticAnalysis CASL CASLBasicSpec CASLFORMULA ()
               SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol where
         basic_analysis CASL = Just $ basicCASLAnalysis
         stat_symb_map_items CASL = statSymbMapItems
         stat_symb_items CASL = statSymbItems
         ensures_amalgamability CASL (opts, diag, sink, desc) =
             ensuresAmalgamability opts diag sink desc

         sign_to_basic_spec CASL _sigma _sens = Basic_spec [] -- ???

         symbol_to_raw CASL = symbolToRaw
         id_to_raw CASL = idToRaw
         matches CASL = CASL.Morphism.matches
         is_transportable CASL = isSortInjective

         empty_signature CASL = emptySign ()
         signature_union CASL sigma1 sigma2 =
           return $ addSig dummy sigma1 sigma2
         morphism_union CASL = morphismUnion (const id) dummy
         final_union CASL = finalUnion dummy
         is_subsig CASL = isSubSig trueC
         inclusion CASL = sigInclusion dummy trueC
         cogenerated_sign CASL = cogeneratedSign dummy
         generated_sign CASL = generatedSign dummy
         induced_from_morphism CASL = inducedFromMorphism dummy
         induced_from_to_morphism CASL = inducedFromToMorphism dummy trueC
         theory_to_taxonomy CASL = convTaxo


instance Logic CASL CASL.Sublogic.CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol () where

         stability _ = Stable

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
         proj_sublogic_epsilon CASL = CASL.Sublogic.pr_epsilon dummy
         proj_sublogic_symbol CASL = CASL.Sublogic.pr_symbol
