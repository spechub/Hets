
-- needs ghc -fglasgow-exts -fallow-overlapping-instances -package data

{- HetCATS/Logic.hs
   $Id$
   Till Mossakowski, Christian Maeder
   
   Provides data structures for logics (with symbols). Logics are
   a type class with an "identitiy" type (usually interpreted
   by a singleton set) which serves to treat logics as 
   data. All the functions in the type class take the
   identity as first argument in order to determine the logic.

   For logic representations see LogicRepr.hs

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
   
-}

module Logic where

import Id
import AS_Annotation

import Set
import FiniteMap
import Graph
import Result
import Parsec
import Prover -- for one half of class Sentences

import PrettyPrint

import Dynamic

-- for coercion used in LogicGraph.hs and Grothendieck.hs
import GlaExts(unsafeCoerce#)

-- maps

type EndoMap a = FiniteMap a a

-- diagrams are just graphs

data Diagram object morphism = Graph object morphism

-- languages, define like "data CASL = CASL deriving Show" 

class Show id => Language id where
    language_name :: id -> String
    language_name i = show i

-- (a bit unsafe) coercion using the language name
coerce :: (Language id1, Language id2) => id1 -> id2 -> a -> Maybe b
coerce i1 i2 a = if language_name i1 == language_name i2 then 
		 (Just $ unsafeCoerce# a) else Nothing

-- Categories are given by a quotient,
-- i.e. we need equality
-- Should we allow arbitrary composition graphs and build paths?

class (Language id, Eq sign, Show sign, Eq morphism) => 
      Category id sign morphism | id -> sign, id -> morphism where
         ide :: id -> sign -> morphism
         o :: id -> morphism -> morphism -> Maybe morphism
         dom, cod :: id -> morphism -> sign
         legal_obj :: id -> sign -> Bool
         legal_mor :: id -> morphism -> Bool

-- abstract syntax, parsing and printing

class (Language id, PrettyPrint basic_spec, Eq basic_spec,
       PrettyPrint symb_items, Eq symb_items,
       PrettyPrint symb_map_items, Eq symb_map_items) =>
      Syntax id basic_spec symb_items symb_map_items
        | id -> basic_spec, id -> symb_items,
          id -> symb_map_items
      where 
         -- parsing
         parse_basic_spec :: id -> Maybe(GenParser Char st basic_spec)
         parse_symb_items :: id -> GenParser Char st symb_items
         parse_symb_map_items :: id -> GenParser Char st symb_map_items

-- sentences (plus prover stuff and "symbol" with "Ord" for efficient lookup)

class (Category id sign morphism, Show sentence, 
       Show local_env, Ord symbol, Show symbol)
    => Sentences id sentence local_env sign morphism symbol
        | id -> sentence, id -> local_env, id -> sign, id -> morphism,
          id -> symbol
      where
         -- sentence translation
      map_sen :: id -> morphism -> sentence -> Result sentence
         -- parsing of sentences
      parse_sentence :: id -> local_env -> String -> Result sentence
           -- is a term parser needed as well?
      provers :: id -> [Prover sentence symbol]
      cons_checkers :: id -> [Cons_checker 
			      (TheoryMorphism sign sentence morphism)] 
-- static analysis

class ( Syntax id basic_spec symb_items symb_map_items
      , Sentences id sentence local_env sign morphism symbol
      , Show raw_symbol, Eq raw_symbol)
    => StaticAnalysis id 
        basic_spec sentence symb_items symb_map_items
        local_env sign morphism symbol raw_symbol 
        | id -> basic_spec, id -> sentence, id -> symb_items,
          id -> symb_map_items, id -> local_env,
          id -> sign, id -> morphism, id -> symbol, id -> raw_symbol
      where
         -- static analysis of basic specifications and symbol maps
         basic_analysis :: id -> 
                           Maybe((basic_spec,  -- abstract syntax tree
                            local_env,   -- efficient table for env signature
                            [Annotation]) ->   -- global annotations
                           Result (local_env,sign,[(String,sentence)]))
                              -- the output local env is expected to be
                              -- just the input local env, united with the sign.
                              -- We have both just for efficiency reasons.
                              -- These include any new annotations
         stat_symb_map_items :: 
	     id -> symb_map_items -> Result (EndoMap raw_symbol)
         stat_symb_items :: id -> symb_items -> Result [raw_symbol] 
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
         empty_local_env :: id -> local_env
         add_sign :: id -> sign -> local_env -> local_env
         empty_signature :: id -> sign
         signature_union :: id -> sign -> sign -> Result sign
         final_union :: id -> sign -> sign -> Result sign
         is_subsig :: id -> sign -> sign -> Bool
         generated_sign, cogenerated_sign :: 
	     id -> [raw_symbol] -> sign -> Result morphism
         induced_from_morphism :: 
	     id -> EndoMap raw_symbol -> sign -> Result morphism
         induced_from_to_morphism :: 
	     id -> EndoMap raw_symbol -> sign -> sign -> Result morphism 
         extend_morphism :: 
	     id -> sign -> morphism -> sign -> sign -> Result morphism

-- sublogics

class Ord l => LatticeWithTop l where
  meet, join :: l -> l -> l
  top :: l


-- logics

class (StaticAnalysis id 
        basic_spec sentence symb_items symb_map_items
        local_env sign morphism symbol raw_symbol,
       LatticeWithTop sublogics, Typeable sublogics) =>
      Logic id sublogics
        basic_spec sentence symb_items symb_map_items
        local_env sign morphism symbol raw_symbol 
        | id -> sublogics, id -> basic_spec, id -> sentence, id -> symb_items,
          id -> symb_map_items, id -> local_env,
          id -> sign, id -> morphism, id ->symbol, id -> raw_symbol
	  where
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