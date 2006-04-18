{-# OPTIONS -fallow-undecidable-instances #-}
{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable (various -fglasgow-exts extensions)

Provides data structures for logics (with symbols). Logics are
   a type class with an /identity/ type (usually interpreted
   by a singleton set) which serves to treat logics as
   data. All the functions in the type class take the
   identity as first argument in order to determine the logic.

   For logic (co)morphisms see "Logic.Comorphism"

   This module uses multiparameter type classes
   (<http://haskell.org/ghc/docs/latest/html/users_guide/type-extensions.html#multi-param-type-classes>)
   with functional dependencies (<http://haskell.org/hawiki/FunDeps>)
   for defining an interface for the notion of logic. Multiparameter type
   classes are needed because a logic consists of a collection of types,
   together with operations on these. Functional dependencies
   are needed because no operation will involve all types of
   the multiparameter type class; hence we need a method to derive
   the missing types. We chose an easy way: for each logic, we
   introduce a new singleton type that constitutes the identity
   of the logic. All other types of the multiparameter type class
   depend on this 'identy constituting' type, and all operations take
   the 'identity constituting' type as first arguments. The value
   of the argument of the 'identity constituting' type is irrelevant
   (note that there is only one value of such a type anyway).

   References:

   J. A. Goguen and R. M. Burstall
   Institutions: Abstract Model Theory for Specification and
     Programming
   JACM 39, p. 95--146, 1992
   (general notion of logic - model theory only)

   J. Meseguer
   General Logics
   Logic Colloquium 87, p. 275--329, North Holland, 1989
   (general notion of logic - also proof theory;
    notion of logic representation, called map there)

   T. Mossakowski:
   Specification in an arbitrary institution with symbols
   14th WADT 1999, LNCS 1827, p. 252--270
   (treatment of symbols and raw symbols, see also CASL semantics)

   T. Mossakowski, B. Klin:
   Institution Independent Static Analysis for CASL
   15h WADT 2001, LNCS 2267, p. 221-237, 2002.
   (what is needed for static anaylsis)

   S. Autexier and T. Mossakowski
   Integrating HOLCASL into the Development Graph Manager MAYA
   FroCoS 2002, to appear
   (interface to provers)

   Todo:
   ATerm, XML
   Weak amalgamability
   Metavars
   raw symbols are now symbols, symbols are now signature symbols
   provide both signature symbol set and symbol set of a signature
   introduce coercion safer functions (separately for each type)
-}

module Logic.Logic where

import Common.Id
import Common.GlobalAnnotations
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Map as Map
import Common.Lib.Graph as Tree
import Common.Lib.Pretty
import Common.AnnoState
import Common.Result
import Common.AS_Annotation
import Common.Print_AS_Annotation
import Logic.Prover -- for one half of class Sentences

import Common.PrettyPrint
import Common.DynamicUtils
import Common.ATerm.Lib -- (ShATermConvertible)
import ATC.DefaultMorphism()
import Common.Amalgamate -- passed to ensures_amalgamability
import Common.Taxonomy
import Taxonomy.MMiSSOntology (MMiSSOntology)

-- | Stability of logic implementations
data Stability = Stable | Testing | Unstable | Experimental
     deriving (Eq,Show)

-- | shortcut for class constraints
class (Show a, PrettyPrint a, PrintLaTeX a, Typeable a, ShATermConvertible a)
    => PrintTypeConv a

-- | shortcut for class constraints with equality
class (Eq a, PrintTypeConv a) => EqPrintTypeConv a

instance (Show a, PrettyPrint a, PrintLaTeX a, Typeable a,
               ShATermConvertible a) => PrintTypeConv a
instance (Eq a, PrintTypeConv a) => EqPrintTypeConv a

type EndoMap a = Map.Map a a

-- languages, define like "data CASL = CASL deriving Show"

class Show lid => Language lid where
    language_name :: lid -> String
    language_name i = show i
    description :: lid -> String
    -- default implementation
    description _ = "No description available"

-- Categories are given by a quotient,
-- i.e. we need equality
-- Should we allow arbitrary composition graphs and build paths?

class (Language lid, Eq sign, Eq morphism)
    => Category lid sign morphism | lid -> sign morphism where
         ide :: lid -> sign -> morphism
         comp :: lid -> morphism -> morphism -> Result morphism
           -- diagrammatic order
         dom, cod :: lid -> morphism -> sign
         legal_obj :: lid -> sign -> Bool
         legal_mor :: lid -> morphism -> Bool

-- abstract syntax, parsing and printing

class (Language lid, PrintTypeConv basic_spec,
       EqPrintTypeConv symb_items,
       EqPrintTypeConv symb_map_items)
    => Syntax lid basic_spec symb_items symb_map_items
        | lid -> basic_spec symb_items symb_map_items
      where
         -- parsing
         parse_basic_spec :: lid -> Maybe(AParser st basic_spec)
         parse_symb_items :: lid -> Maybe(AParser st symb_items)
         parse_symb_map_items :: lid -> Maybe(AParser st symb_map_items)
         -- default implementations
         parse_basic_spec _ = Nothing
         parse_symb_items _ = Nothing
         parse_symb_map_items _ = Nothing

-- sentences (plus prover stuff and "symbol" with "Ord" for efficient lookup)

class (Category lid sign morphism, Ord sentence,
       Ord symbol,
       PrintTypeConv sign, PrintTypeConv morphism,
       PrintTypeConv sentence, PrintTypeConv symbol,
       Eq proof_tree, Show proof_tree, ShATermConvertible proof_tree,
       Ord proof_tree, Typeable proof_tree)
    => Sentences lid sentence proof_tree sign morphism symbol
        | lid -> sentence proof_tree sign morphism symbol
      where
         -- sentence translation
      map_sen :: lid -> morphism -> sentence -> Result sentence
      map_sen l _ _ = statErr l "map_sen"
         -- simplification of sentences (leave out qualifications)
      simplify_sen :: lid -> sign -> sentence -> sentence
      simplify_sen _ _ = id  -- default implementation
         -- parsing of sentences
      parse_sentence :: lid -> Maybe (AParser st sentence)
      parse_sentence _ = Nothing
           -- print a sentence with comments
      print_named :: lid -> GlobalAnnos -> Named sentence -> Doc
      print_named _ = printLabelledSen
      sym_of :: lid -> sign -> Set.Set symbol
      symmap_of :: lid -> morphism -> EndoMap symbol
      sym_name :: lid -> symbol -> Id
      provers :: lid -> [Prover sign sentence proof_tree]
      provers _ = []
      cons_checkers :: lid -> [ConsChecker sign sentence morphism proof_tree]
      cons_checkers _ = []
      conservativityCheck :: lid -> (sign, [Named sentence]) ->
                       morphism -> [Named sentence] -> Result (Maybe Bool)
      conservativityCheck l _ _ _ = statErr l "conservativityCheck"

-- | a dummy function to allow type checking *.inline.hs files
inlineAxioms :: StaticAnalysis lid
        basic_spec sentence proof_tree symb_items symb_map_items
        sign morphism symbol raw_symbol => lid -> String -> [Named sentence]
inlineAxioms _ _ = error "inlineAxioms"

-- static analysis
statErr :: (Language lid, Monad m) => lid -> String -> m a
statErr lid str = fail ("Logic." ++ str ++ " nyi for: " ++ language_name lid)

class ( Syntax lid basic_spec symb_items symb_map_items
      , Sentences lid sentence proof_tree sign morphism symbol
      , Ord raw_symbol, PrintLaTeX raw_symbol, Typeable raw_symbol)
    => StaticAnalysis lid
        basic_spec sentence proof_tree symb_items symb_map_items
        sign morphism symbol raw_symbol
        | lid -> basic_spec sentence proof_tree symb_items symb_map_items
                 sign morphism symbol raw_symbol
      where
         -- static analysis of basic specifications and symbol maps
         basic_analysis :: lid ->
                           Maybe((basic_spec,  -- abstract syntax tree
                            sign,   -- efficient table for env signature
                            GlobalAnnos) ->   -- global annotations
                           Result (basic_spec,sign,sign,[Named sentence]))
                           -- the resulting bspec has analyzed axioms in it
                           -- sign's: sigma_local, sigma_complete, i.e.
                           -- the second output sign united with the input sign
                           -- should yield the first output sign
                           -- the second output sign is the accumulated sign
         -- default implementation
         basic_analysis _ = Nothing

         -- Shouldn't the following deliver Maybes???
         sign_to_basic_spec :: lid -> sign -> [Named sentence] -> basic_spec
         stat_symb_map_items ::
             lid -> [symb_map_items] -> Result (EndoMap raw_symbol)
         stat_symb_map_items _ _ = fail "Logic.stat_symb_map_items"
         stat_symb_items :: lid -> [symb_items] -> Result [raw_symbol]
         stat_symb_items l _ = statErr l "stat_symb_items"
         -- amalgamation
         weaklyAmalgamableCocone :: lid -> Tree.Gr sign morphism
                                     -> Result (sign, Map.Map Int morphism)
         weaklyAmalgamableCocone l _ = statErr l "weaklyAmalgamableCocone"
         -- architectural sharing analysis
         ensures_amalgamability :: lid ->
              ([CASLAmalgOpt],        -- the program options
               Tree.Gr sign morphism, -- the diagram to be analyzed
               [(Int, morphism)],     -- the sink
               Tree.Gr String String) -- the descriptions of nodes and edges
                  -> Result Amalgamates
         ensures_amalgamability l _ = statErr l "ensures_amalgamability"
         -- symbols and symbol maps
         symbol_to_raw :: lid -> symbol -> raw_symbol
         id_to_raw :: lid -> Id -> raw_symbol
         matches :: lid -> symbol -> raw_symbol -> Bool

         -- operations on signatures and morphisms
         empty_signature :: lid -> sign
         signature_union :: lid -> sign -> sign -> Result sign
         signature_union l _ _ = statErr l "signature_union"
         morphism_union :: lid -> morphism -> morphism -> Result morphism
         morphism_union l _ _ = statErr l "morphism_union"
         final_union :: lid -> sign -> sign -> Result sign
         final_union l _ _ = statErr l "final_union"
         is_transportable :: lid -> morphism -> Bool
         is_transportable l _ =
            error ("Logic.is_transportable nyi for logic"++language_name l)

           -- see CASL reference manual, III.4.1.2
         is_subsig :: lid -> sign -> sign -> Bool
         inclusion :: lid -> sign -> sign -> Result morphism
         inclusion l _ _ = statErr l "inclusion"
         generated_sign, cogenerated_sign ::
             lid -> Set.Set symbol -> sign -> Result morphism
         generated_sign l _ _ = statErr l "generated_sign"
         cogenerated_sign l _ _ = statErr l "cogenerated_sign"
         induced_from_morphism ::
             lid -> EndoMap raw_symbol -> sign -> Result morphism
         induced_from_morphism l _ _ = statErr l "induced_from_morphism"
         induced_from_to_morphism ::
             lid -> EndoMap raw_symbol -> sign -> sign -> Result morphism
         induced_from_to_morphism l _ _ _ =
             statErr l "induced_from_to_morphism"
         -- generate taxonomy from theory
         theory_to_taxonomy :: lid
                            -> TaxoGraphKind
                            -> MMiSSOntology
                            -> sign -> [Named sentence]
                            -> Result MMiSSOntology
         theory_to_taxonomy l _ _ _ _ = statErr l "theory_to_taxonomy"

-- sublogics

class (Eq l, Show l) => LatticeWithTop l where
  meet, join :: l -> l -> l
  top :: l
  isSubElem :: l -> l -> Bool
  isSubElem a b = join a b == b

instance LatticeWithTop () where
  meet _ _ = ()
  join _ _ = ()
  top = ()

-- logics

class (StaticAnalysis lid
        basic_spec sentence proof_tree symb_items symb_map_items
        sign morphism symbol raw_symbol,
       LatticeWithTop sublogics, ShATermConvertible sublogics,
       Typeable sublogics)
    => Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        | lid -> sublogics
                 basic_spec sentence symb_items symb_map_items
                 sign morphism symbol raw_symbol proof_tree
          where

         -- stability of the implementation
         stability :: lid -> Stability
         -- default
         stability _ = Experimental

         -- for a process logic, return its data logic
         data_logic :: lid -> Maybe AnyLogic
         data_logic _ = Nothing

         sublogic_names :: lid -> sublogics -> [String]
         sublogic_names lid _ = [language_name lid]
             -- the first name is the principal name
         all_sublogics :: lid -> [sublogics]
         all_sublogics _ = [top]

         is_in_basic_spec :: lid -> sublogics -> basic_spec -> Bool
         is_in_basic_spec _ _ _ = False
         is_in_sentence :: lid -> sublogics -> sentence -> Bool
         is_in_sentence _ _ _ = False
         is_in_symb_items :: lid -> sublogics -> symb_items -> Bool
         is_in_symb_items _ _ _ = False
         is_in_symb_map_items :: lid -> sublogics -> symb_map_items -> Bool
         is_in_symb_map_items _ _ _ = False
         is_in_sign :: lid -> sublogics -> sign -> Bool
         is_in_sign _ _ _ = False
         is_in_morphism :: lid -> sublogics -> morphism -> Bool
         is_in_morphism _ _ _ = False
         is_in_symbol :: lid -> sublogics -> symbol -> Bool
         is_in_symbol _ _ _ = False

         min_sublogic_basic_spec :: lid -> basic_spec -> sublogics
         min_sublogic_basic_spec _ _ = top
         min_sublogic_sentence :: lid -> sentence -> sublogics
         min_sublogic_sentence _ _ = top
         min_sublogic_symb_items :: lid -> symb_items -> sublogics
         min_sublogic_symb_items _ _ = top
         min_sublogic_symb_map_items :: lid -> symb_map_items -> sublogics
         min_sublogic_symb_map_items _ _ = top
         min_sublogic_sign :: lid -> sign -> sublogics
         min_sublogic_sign _ _ = top
         min_sublogic_morphism :: lid -> morphism -> sublogics
         min_sublogic_morphism _ _ = top
         min_sublogic_symbol :: lid -> symbol -> sublogics
         min_sublogic_symbol _ _ = top
         proj_sublogic_basic_spec :: lid -> sublogics
                                  -> basic_spec -> basic_spec
         proj_sublogic_basic_spec _ _ b = b
         proj_sublogic_symb_items :: lid -> sublogics
                                  -> symb_items -> Maybe symb_items
         proj_sublogic_symb_items _ _ _ = Nothing
         proj_sublogic_symb_map_items :: lid -> sublogics
                                      -> symb_map_items -> Maybe symb_map_items
         proj_sublogic_symb_map_items _ _ _ = Nothing
         proj_sublogic_sign :: lid -> sublogics -> sign -> sign
         proj_sublogic_sign _ _ s = s
         proj_sublogic_morphism :: lid -> sublogics -> morphism -> morphism
         proj_sublogic_morphism _ _ m = m
         proj_sublogic_epsilon :: lid -> sublogics -> sign -> morphism
         proj_sublogic_epsilon li _ s = ide li s
         proj_sublogic_symbol :: lid -> sublogics -> symbol -> Maybe symbol
         proj_sublogic_symbol _ _ _ = Nothing

         top_sublogic :: lid -> sublogics
         top_sublogic _ = top

----------------------------------------------------------------
-- Derived functions
----------------------------------------------------------------

empty_theory :: StaticAnalysis lid
        basic_spec sentence proof_tree symb_items symb_map_items
        sign morphism symbol raw_symbol =>
        lid -> Theory sign sentence proof_tree
empty_theory lid = Theory (empty_signature lid) Map.empty

----------------------------------------------------------------
-- Existential type covering any logic
----------------------------------------------------------------

data AnyLogic = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree =>
        Logic lid

instance Show AnyLogic where
  show (Logic lid) = language_name lid
instance Eq AnyLogic where
  Logic lid1 == Logic lid2 = language_name lid1 == language_name lid2

tyconAnyLogic :: TyCon
tyconAnyLogic = mkTyCon "Logic.Logic.AnyLogic"
instance Typeable AnyLogic where
  typeOf _ = mkTyConApp tyconAnyLogic []

{- class hierarchy:
                            Language
               __________/
   Category
      |                  /
   Sentences      Syntax
      \            /
      StaticAnalysis (no sublogics)
            \
             \
            Logic

-}
