{-# OPTIONS -fallow-undecidable-instances #-}
{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, and Uni Bremen 2002-2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable (various -fglasgow-exts extensions)
 
   
   Provides data structures for logics (with symbols). Logics are
   a type class with an "identitiy" type (usually interpreted
   by a singleton set) which serves to treat logics as 
   data. All the functions in the type class take the
   identity as first argument in order to determine the logic.

   For logic (co)morphisms see Comorphism.hs

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
   
-}

module Logic.Logic where

import Common.Id
import Common.GlobalAnnotations
import Common.Lib.Set
import Common.Lib.Map
import Common.Lib.Graph
import Common.Lib.Pretty
import Common.AnnoState
import Common.Result
import Common.AS_Annotation
import Common.Print_AS_Annotation
import Logic.Prover -- for one half of class Sentences

import Common.PrettyPrint
import Data.Dynamic
import Common.DynamicUtils 

-- for coercion used in Grothendieck.hs and Analysis modules

import UnsafeCoerce

-- for Conversion to ATerms 
import Common.ATerm.Lib -- (ATermConvertible)

-- for HetcatsOpts passed to ensures_amalgamability
import Options

-- diagrams are just graphs
type Diagram object morphism = Graph object morphism

-- | Amalgamability analysis might be undecidable, so we need
-- a special type for the result of ensures_amalgamability
data Amalgamates = Yes
		 | No String       -- ^ failure description
		 | DontKnow String -- ^ the reason for unknown status
-- | The default value for 'DontKnow' amalgamability result
defaultDontKnow :: Amalgamates
defaultDontKnow = DontKnow "Unable to assert that amalgamability is ensured"


-- languages, define like "data CASL = CASL deriving Show" 

class Show lid => Language lid where
    language_name :: lid -> String
    language_name i = show i
    description :: lid -> String
    -- default implementation
    description _ = "No description available"

-- (a bit unsafe) coercion using the language name
coerce :: (Typeable a, Typeable b, Language lid1, Language lid2,
          Monad m) => lid1 -> lid2 -> a -> m b
coerce i1 i2 a = if language_name i1 == language_name i2 
                 then return $ unsafeCoerce a 
                 else fail ("Logic "++ language_name i1 ++ " expected, but "
                            ++ language_name i2 ++ " found")

rcoerce :: (Typeable a, Typeable b, Language lid1, Language lid2) => 
           lid1 -> lid2 -> Pos-> a -> Result b
rcoerce i1 i2 pos a = adjustPos pos $ coerce i1 i2 a

-- Categories are given by a quotient,
-- i.e. we need equality
-- Should we allow arbitrary composition graphs and build paths?

class (PrintLaTeX a, Typeable a, ATermConvertible a) => PrintTypeConv a
class (Eq a, PrintTypeConv a) => EqPrintTypeConv a

instance (PrintLaTeX a, Typeable a, ATermConvertible a) => PrintTypeConv a
instance (Eq a, PrintTypeConv a) => EqPrintTypeConv a

class (Language lid, Eq sign, Eq morphism)
    => Category lid sign morphism | lid -> sign, lid -> morphism where
         ide :: lid -> sign -> morphism
         comp :: lid -> morphism -> morphism -> Maybe morphism
           -- diagrammatic order
         dom, cod :: lid -> morphism -> sign
         legal_obj :: lid -> sign -> Bool
         legal_mor :: lid -> morphism -> Bool

-- abstract syntax, parsing and printing

class (Language lid, PrintTypeConv basic_spec, 
       EqPrintTypeConv symb_items, 
       EqPrintTypeConv symb_map_items) 
    => Syntax lid basic_spec symb_items symb_map_items
        | lid -> basic_spec, lid -> symb_items,
          lid -> symb_map_items
      where 
         -- parsing
         parse_basic_spec :: lid -> Maybe(AParser basic_spec)
         parse_symb_items :: lid -> Maybe(AParser symb_items)
         parse_symb_map_items :: lid -> Maybe(AParser symb_map_items)
         -- default implementations
         parse_basic_spec _ = Nothing
         parse_symb_items _ = Nothing
         parse_symb_map_items _ = Nothing

-- sentences (plus prover stuff and "symbol" with "Ord" for efficient lookup)

class (Category lid sign morphism, Ord sentence,
       Ord symbol, 
       PrintTypeConv sign, PrintTypeConv morphism,
       PrintTypeConv sentence, PrintTypeConv symbol,
       Eq proof_tree, Show proof_tree, ATermConvertible proof_tree, Typeable proof_tree)
    => Sentences lid sentence proof_tree sign morphism symbol
        | lid -> sentence, lid -> sign, lid -> morphism,
          lid -> symbol, lid -> proof_tree
      where
         -- sentence translation
      map_sen :: lid -> morphism -> sentence -> Result sentence
         -- simplification of sentences (leave out qualifications)
      simplify_sen :: lid -> sign -> sentence -> sentence
      simplify_sen _ _ = id  -- default implementation
         -- parsing of sentences
      parse_sentence :: lid -> Maybe (sign -> String -> Result sentence)
           -- is a term parser needed as well?
      print_named :: lid -> GlobalAnnos -> Named sentence -> Doc
           -- print a sentence with comments
      sym_of :: lid -> sign -> Set symbol
      symmap_of :: lid -> morphism -> EndoMap symbol
      sym_name :: lid -> symbol -> Id 
      provers :: lid -> [Prover sign sentence proof_tree symbol]
      cons_checkers :: lid -> [Cons_checker 
			      (TheoryMorphism sign sentence morphism)] 
      consCheck :: lid -> (sign,[Named sentence]) -> 
                       morphism -> [Named sentence] -> Result (Maybe Bool)
      -- default implementations
      parse_sentence _ = Nothing
      print_named _ = printText0
      provers _ = []
      cons_checkers _ = []

-- static analysis

class ( Syntax lid basic_spec symb_items symb_map_items
      , Sentences lid sentence proof_tree sign morphism symbol
      , Ord raw_symbol, PrintLaTeX raw_symbol, Typeable raw_symbol)
    => StaticAnalysis lid 
        basic_spec sentence proof_tree symb_items symb_map_items
        sign morphism symbol raw_symbol 
        | lid -> basic_spec, lid -> sentence, lid -> symb_items,
          lid -> symb_map_items, lid -> proof_tree,
          lid -> sign, lid -> morphism, lid -> symbol, lid -> raw_symbol
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
         stat_symb_items :: lid -> [symb_items] -> Result [raw_symbol] 
         -- architectural sharing analysis
         ensures_amalgamability :: lid ->
              (HetcatsOpts,            -- the program options
	       Diagram sign morphism, -- the diagram to be analyzed
	       [(Node, morphism)],    -- the sink
	       Diagram String String) -- the descriptions of nodes and edges
		  -> Result Amalgamates

         -- symbols and symbol maps
         symbol_to_raw :: lid -> symbol -> raw_symbol
         id_to_raw :: lid -> Id -> raw_symbol 
         matches :: lid -> symbol -> raw_symbol -> Bool
   
         -- operations on signatures and morphisms
         empty_signature :: lid -> sign
         signature_union :: lid -> sign -> sign -> Result sign
         morphism_union :: lid -> morphism -> morphism -> Result morphism
         final_union :: lid -> sign -> sign -> Result sign
           -- see CASL reference manual, III.4.1.2
         is_subsig :: lid -> sign -> sign -> Bool
         inclusion :: lid -> sign -> sign -> Result morphism
         generated_sign, cogenerated_sign :: 
	     lid -> Set symbol -> sign -> Result morphism
         induced_from_morphism :: 
	     lid -> EndoMap raw_symbol -> sign -> Result morphism
         induced_from_to_morphism :: 
	     lid -> EndoMap raw_symbol -> sign -> sign -> Result morphism 

-- sublogics

class (Ord l, Show l) => LatticeWithTop l where
  meet, join :: l -> l -> l
  top :: l

-- a dummy instance 
instance LatticeWithTop () where
  meet _ _ = ()
  join _ _ = ()
  top = ()

-- logics

class (StaticAnalysis lid 
        basic_spec sentence proof_tree symb_items symb_map_items
        sign morphism symbol raw_symbol,
       LatticeWithTop sublogics, ATermConvertible sublogics,
       Typeable sublogics) 
    => Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        | lid -> sublogics, lid -> basic_spec, lid -> sentence, 
          lid -> symb_items, lid -> symb_map_items, lid -> proof_tree,
          lid -> sign, lid -> morphism, lid ->symbol, lid -> raw_symbol
	  where

         -- for a process logic, return its data logic
         data_logic :: lid -> Maybe AnyLogic
	 data_logic _ = Nothing

         sublogic_names :: lid -> sublogics -> [String] 
	 sublogic_names lid _ = [language_name lid]
             -- the first name is the principal name
         all_sublogics :: lid -> [sublogics]
	 all_sublogics _ = []

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
         min_sublogic_sentence :: lid -> sentence -> sublogics
         min_sublogic_symb_items :: lid -> symb_items -> sublogics
         min_sublogic_symb_map_items :: lid -> symb_map_items -> sublogics
         min_sublogic_sign :: lid -> sign -> sublogics
         min_sublogic_morphism :: lid -> morphism -> sublogics
         min_sublogic_symbol :: lid -> symbol -> sublogics

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

----------------------------------------------------------------
-- Typeable instances
----------------------------------------------------------------

proverTc :: TyCon
proverTc      = mkTyCon "Logic.Prover.Prover"
instance Typeable (Prover sign sen proof_tree symbol) where
    typeOf _ = mkTyConApp proverTc []

namedTc :: TyCon
namedTc = mkTyCon "Common.AS_Annotation.Named"

instance Typeable s => Typeable (Named s) where 
  typeOf s = mkTyConApp namedTc [typeOf ((undefined :: Named a -> a) s)]

setTc :: TyCon
setTc = mkTyCon "Common.Lib.Set.Set"

instance Typeable a => Typeable (Set a) where
  typeOf s = mkTyConApp setTc [typeOf ((undefined:: Set a -> a) s)]

mapTc :: TyCon
mapTc = mkTyCon "Common.Lib.Map.Map"

instance (Typeable a, Typeable b) => Typeable (Map a b) where
  typeOf m = mkTyConApp mapTc [typeOf ((undefined :: Map a b -> a) m),
                            typeOf ((undefined :: Map a b -> b) m)]

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
