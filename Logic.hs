-- needs ghc -fglasgow-exts -package data

{- HetCATS/Logic.hs
   $Id$
   Till Mossakowski
   
   Provides data structures for logics (with symbols)
   and logic representations. Logics are
   a type class with an "identitiy" type (usually interpreted
   by a singleton set) which serves to treat logics as 
   data. All the functions in the type class take the
   identity as first argument in order to determine the logic.
   Logic representations are just collections of
   functions between (some of) the types of logics.

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
   Weak amalgamability, also for reprs
   Metavars
   repr maps
   reprs out of sublogic relationships
-}

module Logic where

import Id
import AS_Annotation
import Set
import FiniteMap
import Graph
import Error
import Dynamic

-- maps

type EndoMap a = FiniteMap a a


-- diagrams are just graphs

data Diagram object morphism = Graph object morphism



-- Categories are given by a quotient,
-- i.e. we need equality
-- Should we allow arbitrary composition graphs and build paths?

class (Eq object, Eq morphism) => 
      Category id object morphism | id -> object, id -> morphism where
         ide :: id -> object -> morphism
         o :: id -> morphism -> morphism -> Maybe morphism
         dom, cod :: id -> morphism -> object
         legal_obj :: id -> object -> Bool
         legal_mor :: id -> morphism -> Bool


-- abstract syntax, parsing and printing

class (Show basic_spec, Eq basic_spec, Show sentence, Show symb_items, 
       Show symb_map_items, Eq symb_items, Eq symb_map_items) =>
      Syntax id basic_spec sentence symb_items symb_map_items
      where 
         -- parsing
         parse_basic_spec :: id -> String -> Result basic_spec
         parse_symb_items :: id -> String -> Result [symb_items]
         parse_symb_map_items :: id -> String -> Result [symb_map_items]
         comment_line :: id -> String
         comment_group :: id -> (String,String)


-- lattices (for sublogics)

class Ord l => LatticeWithTop l where
  meet, join :: l -> l -> l
  top :: l


-- theories and theory morphisms

data Theory sign sen = 
     Theory {sign_of :: sign, 
             ax_of :: [(String,sen)]
            }

data TheoryMorphism sign sen mor = 
     TheoryMorphism {t_source, t_target :: Theory sign sen,
                     t_morphism :: mor
                    } 


-- proofs and provers

type Rule = String

data Proof_tree sen = Axiom sen
                    | Branch (sen,Rule,[Proof_tree sen])  -- add substitutions here?

type Tactic_script = String  -- the file name

data Proof_status sen = Open sen
                      | Disproved sen 
                      | Proved(sen,
                               [sen], -- used axioms
                               Proof_tree sen,
                               Tactic_script)

data Prover sen symbol = 
     Prover { prover_name :: String,
              prover_sublogic :: String,
              add_sym :: symbol -> IO(Bool),  -- returns True if succeeded
              remove_sym :: symbol -> IO(Bool), -- returns True if succeeded
              add_sen :: sen -> IO(Bool),  -- returns True if succeeded
              remove_sen :: sen -> IO(Bool), -- returns True if succeeded
              prove :: sen -> IO([Proof_status sen]) -- proof status for goal and lemmas
            }

data Cons_checker morphism = 
     Cons_checker {cons_checker_name :: String,
                   cons_checker_sublogic :: String,
                   cons_check :: morphism -> IO(Bool, Tactic_script)
                  }


-- logics

class (Syntax id basic_spec sentence symb_items symb_map_items,
       Show sign, Show morphism, Show symbol, Show raw_symbol,
       Ord symbol, --  needed for efficient symbol tables
       Eq raw_symbol,
       Category id sign morphism,
       LatticeWithTop sublogics,
       -- needed for heterogeneous coercions:
       Typeable id, Typeable sublogics, Typeable sign, Typeable morphism, Typeable symbol, Typeable raw_symbol,
       Typeable basic_spec, Typeable sentence, Typeable symb_items, Typeable symb_map_items) =>
      Logic id sublogics
        basic_spec sentence symb_items symb_map_items
        local_env sign morphism symbol raw_symbol 
        | id -> sublogics, id -> basic_spec, id -> sentence, id -> symb_items,
          id -> symb_map_items, id -> local_env,
          id -> sign, id -> morphism, id ->symbol, id -> raw_symbol
       where
         logic_name :: id -> String
         has_parser :: id -> Bool
         has_printer :: id -> Bool
         has_analysis :: id -> Bool

         -- sentence translation
         map_sen :: id -> morphism -> sentence -> Result sentence

         -- parsing of sentences
         parse_sentence :: id -> local_env -> String -> Result sentence
           -- is a term parser needed as well?

         -- static analysis of basic specifications and symbol maps
         basic_analysis :: id -> 
                           (basic_spec,  -- abstract syntax tree
                            local_env,   -- efficient table for env signature
                            [Annotation]) ->   -- global annotations
                           Result (local_env,sign,[(String,sentence)])
                              -- the output local env is expected to be
                              -- just the input local env, united with the sign.
                              -- We have both just for efficiency reasons.
                              -- These include any new annotations
         stat_symb_map_items :: id -> [symb_map_items] -> Result (EndoMap raw_symbol)
         stat_symb_items :: id -> [symb_items] -> Result [raw_symbol] 

         -- architectural sharing analysis for one morphism
         ensures_amalgamability :: id ->
              (Diagram sign morphism, Node, sign, LEdge morphism, morphism) -> 
               Result (Diagram sign morphism)
         -- do we need it also for sinks consisting of two morphisms?

         -- symbols and symbol maps
         symbol_to_raw :: id -> symbol -> raw_symbol
         id_to_raw :: id -> Id -> raw_symbol 
         sym_of :: id -> sign -> Set symbol
         symmap_of :: id -> morphism -> EndoMap symbol
         matches :: id -> symbol -> raw_symbol -> Bool
         sym_name :: id -> symbol -> Id 
   
         -- operations on local envs, signatures and morphisms
         empty_local_env :: local_env
         add_sign :: sign -> local_env -> local_env
         empty_signature :: id -> sign
         signature_union :: id -> sign -> sign -> Result sign
         final_union :: id -> sign -> sign -> Result sign
         is_subsig :: id -> sign -> sign -> Bool
         generated_sign, cogenerated_sign :: id -> [raw_symbol] -> sign -> Result morphism
         induced_from_morphism :: id -> EndoMap raw_symbol -> sign -> Result morphism
         induced_from_to_morphism :: id -> EndoMap raw_symbol -> sign -> sign -> Result morphism 
         extend_morphism :: Id -> sign -> morphism -> sign -> sign -> Result morphism

         -- sublogics
         sublogic_names :: id -> sublogics -> [String] 
             -- the first name is the principal name
         all_sublogics :: id -> [sublogics]

         is_in_basic_spec :: id -> sublogics -> basic_spec -> Bool
         is_in_sentence :: id -> sublogics -> sentence -> Bool
         is_in_symb_items :: id -> sublogics -> symb_items -> Bool
         is_in_symb_map_items :: id -> sublogics -> symb_map_items -> Bool
         is_in_sign :: id -> sublogics -> sign -> Bool
         is_in_morphism :: id -> sublogics -> morphism -> Bool
         is_in_symbol :: id -> sublogics -> symbol -> Bool

         min_sublogic_basic_spec :: id -> basic_spec -> sublogics
         min_sublogic_sentence :: id -> sentence -> sublogics
         min_sublogic_symb_items :: id -> symb_items -> sublogics
         min_sublogic_symb_map_items :: id -> symb_map_items -> sublogics
         min_sublogic_sign :: id -> sign -> sublogics
         min_sublogic_morphism :: id -> morphism -> sublogics
         min_sublogic_symbol :: id -> symbol -> sublogics

         proj_sublogic_basic_spec :: id -> sublogics -> basic_spec -> basic_spec
         proj_sublogic_symb_items :: id -> sublogics -> symb_items -> Maybe symb_items
         proj_sublogic_symb_map_items :: id -> sublogics -> symb_map_items -> Maybe symb_map_items
         proj_sublogic_sign :: id -> sublogics -> sign -> sign 
         proj_sublogic_morphism :: id -> sublogics -> morphism -> morphism
         proj_sublogic_epsilon :: id -> sublogics -> sign -> morphism
         proj_sublogic_symbol :: id -> sublogics -> symbol -> Maybe symbol

         -- provers
         provers :: [Prover sentence symbol]
         cons_checkers :: [Cons_checker (TheoryMorphism sign sentence morphism)] 

         -- derived operations, need not to be given

         -- printing, accessible via logic identity
         show_basic_spec :: id -> basic_spec -> String
         show_sentence :: id -> sentence -> String
         show_symb_items :: id -> symb_items -> String
         show_symb_items_list :: id -> [symb_items] -> String
         show_symb_map_items :: id -> symb_map_items -> String
         show_symb_map_items_list :: id -> [symb_map_items] -> String
         show_sign :: id -> sign -> String
         show_morphism :: id -> morphism -> String
         show_symbol :: id -> symbol -> String
         show_raw_symbol :: id -> raw_symbol -> String 

         show_basic_spec _ = show
         show_sentence _ = show
         show_symb_items _ = show
         show_symb_items_list _ l = showList l ""
         show_symb_map_items _ = show
         show_symb_map_items_list _ l = showList l ""
         show_sign _ = show
         show_morphism _ = show
         show_symbol _ = show
         show_raw_symbol _ = show



-- Simple logic representations (possibly also morphisms via adjointness)

data (Logic id1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        local_env1 sign1 morphism1 symbol1 raw_symbol1,
      Logic id2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2 
        local_env2 sign2 morphism2 symbol2 raw_symbol2) =>
  LogicRepr id1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                local_env1 sign1 morphism1 symbol1 raw_symbol1
            id2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                local_env2 sign2 morphism2 symbol2 raw_symbol2
     =
     LogicRepr {repr_name :: String,
                source :: id1, source_sublogic :: sublogics1,
                target :: id2, target_sublogic :: sublogics2,
                -- the translation functions are partial 
                -- because the target may be a sublanguage
                -- map_basic_spec :: basic_spec1 -> Maybe basic_spec2,
                map_sign :: sign1 -> Maybe (sign2,[sentence2]),
                projection:: Maybe (-- the right adjoint functor Psi
                                    sign2 -> sign1, morphism2 -> morphism1,
                                    -- the counit 
                                    sign2 -> morphism2,
                                    -- basic_spec2 -> basic_spec1,
                                    -- corresponding symbol translation
                                    symbol2 -> Maybe symbol1),  
                map_morphism :: morphism1 -> Maybe morphism2,
                map_sentence :: sign1 -> sentence1 -> Maybe sentence2,
                      -- also covers semi-representations
                      -- with no sentence translation
                map_symbol :: symbol1 -> Set symbol2
                  -- codings may be more complex
               }
