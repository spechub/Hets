{-# LANGUAGE UndecidableInstances #-}
{- |
Module      :  $Header$
Description :  central interface (type class) for logics in Hets
Copyright   :  (c) Till Mossakowski, and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (various -fglasgow-exts extensions)

Central interface (type class) for logics in Hets

Provides data structures for logics (with symbols). Logics are
   a type class with an /identity type/ (usually interpreted
   by a singleton set) which serves to treat logics as
   data. All the functions in the type class take the
   identity as first argument in order to determine the logic.

   For logic (co)morphisms see "Logic.Comorphism"

   This module uses multiparameter type classes with functional dependencies
   (<http://www.haskell.org/haskellwiki/Functional_dependencies>)
   for defining an interface for the notion of logic. Multiparameter type
   classes are needed because a logic consists of a collection of types,
   together with operations on these. Functional dependencies
   are needed because no operation will involve all types of
   the multiparameter type class; hence we need a method to derive
   the missing types. We chose an easy way: for each logic, we
   introduce a new singleton type that is the name, or constitutes the identity
   of the logic. All other types of the multiparameter type class
   depend on this /identity constituting/ type, and all operations take
   the 'identity constituting' type as first arguments. The value
   of the argument of the /identity constituting/ type is irrelevant
   (note that there is only one value of such a type anyway).

   Note that we tend to use @lid@ both for the /identity type/
   of a logic, as well as for its unique inhabitant, i.e. @lid :: lid@.

   The other types involved in the definition of logic are as follows:

   * sign: signatures, that is, contexts, or non-logical vocabularies,
   typically consisting of a set of declared sorts, predicates,
   function symbols, propositional letters etc., together with their
   typing.

   * sentence: logical formulas.

   * basic_spec: abstract syntax of basic specifications. The latter are
   human-readable presentations of a signature together with some sentences.

   * symbol: symbols that may occur in a signature, fully qualified
   with their types

   * raw_symbol:  symbols that may occur in a signature, possibly not
   or partially qualified

   * morphism: maps between signatures (typically preserving the structure).

   * symb_items: abstract syntax of symbol lists, used for declaring some
   symbols of a signature as hidden.

   * symb_map_items: abstract syntax of symbol maps, i.e. human-readable
   presentations of signature morphisms.

   * sublogics: sublogics of the given logic. This type might be a
   record of Boolean flags, indicating whether some feature is
   present in the sublogi of not.

   * proof_tree: proof trees.

   References:

   J. A. Goguen and R. M. Burstall
   Institutions: Abstract Model Theory for Specification and
     Programming
   JACM 39, p. 95-146, 1992
   (general notion of logic - model theory only)

   J. Meseguer
   General Logics
   Logic Colloquium 87, p. 275-329, North Holland, 1989
   (general notion of logic - also proof theory;
    notion of logic representation, called map there)

   T. Mossakowski:
   Specification in an arbitrary institution with symbols
   14th WADT 1999, LNCS 1827, p. 252-270
   (treatment of symbols and raw symbols, see also CASL semantics
    in the CASL reference manual)

   T. Mossakowski, B. Klin:
   Institution Independent Static Analysis for CASL
   15h WADT 2001, LNCS 2267, p. 221-237, 2002.
   (what is needed for static anaylsis)

   S. Autexier and T. Mossakowski
   Integrating HOLCASL into the Development Graph Manager MAYA
   FroCoS 2002, LNCS 2309, p. 2-17, 2002.
   (interface to provers)

   CoFI (ed.): CASL Reference Manual, LNCS 2960, Springer Verlag, 2004.
   (static semantics of CASL structured and architectural specifications)

   T. Mossakowski
   Heterogeneous specification and the heterogeneous tool set
   Habilitation thesis, University of Bremen, 2005
   (the general picture of heterogeneous specification)
-}

module Logic.Logic where

import Logic.Prover (Prover, ConsChecker, Theory(..))
import Taxonomy.MMiSSOntology (MMiSSOntology)
import ATC.DefaultMorphism ()

import Common.AS_Annotation
import ATerm.Lib (ShATermConvertible)
import Common.Amalgamate
import Common.AnnoState
import Common.Consistency
import Common.DefaultMorphism
import Common.Doc
import Common.DocUtils
import Common.ExtSign
import Common.GlobalAnnotations
import Common.Id
import Common.Lib.Graph
import Common.LibName
import Common.Result
import Common.Taxonomy

import Common.Item (Item)

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Typeable

import qualified OMDoc.DataTypes as OMDoc

-- | Stability of logic implementations
data Stability = Stable | Testing | Unstable | Experimental
     deriving (Eq, Show)

-- | shortcut for class constraints
class ShATermConvertible a => Convertible a
instance ShATermConvertible a => Convertible a

-- | shortcut for class constraints
class (Pretty a, Convertible a) => PrintTypeConv a
instance (Pretty a, Convertible a) => PrintTypeConv a

-- | shortcut for class constraints with equality
class (Eq a, PrintTypeConv a) => EqPrintTypeConv a
instance (Eq a, PrintTypeConv a) => EqPrintTypeConv a

-- | maps from a to a
type EndoMap a = Map.Map a a

{- | the name of a logic.
     Define instances like "data CASL = CASL deriving Show"
-}
class Show lid => Language lid where
    language_name :: lid -> String
    language_name i = show i
    description :: lid -> String
    -- default implementation
    description _ = "No description available"

{- | Categories are given as usual: objects, morphisms, identities,
     domain, codomain and composition. The type id is the name, or
     the identity of the category. It is an argument to all functions
     of the type class, serving disambiguation among instances
     (via the functional dependency lid -> object morphism).
     The types for objects and morphisms may be restricted to
     subtypes, using legal_obj and legal_mor. For example, for the
     category of sets and injective maps, legal_mor would check
     injectivity. Since Eq is a subclass of Category, it is also
     possible to impose a quotient on the types for objects and morphisms.
     Require Ord instances only for efficiency, i.e. in sets or maps.
-}
class (Ord object, Ord morphism)
    => Category object morphism | morphism -> object where
         -- | identity morphisms
         ide :: object -> morphism
         -- | composition, in diagrammatic order,
         --   if intermediate objects are equal (not checked!)
         composeMorphisms :: morphism -> morphism -> Result morphism
         -- | domain and codomain of morphisms
         dom, cod :: morphism -> object
         -- | the inverse of a morphism
         inverse :: morphism -> Result morphism
         inverse _ = fail "Logic.Logic.Category.inverse not implemented"
         -- | test if the signature morphism an inclusion
         isInclusion :: morphism -> Bool
         isInclusion _ = False -- in general no inclusion
         -- | is a value of type morphism denoting a legal  morphism?
         legal_mor :: morphism -> Bool

comp :: Category object morphism => morphism -> morphism -> Result morphism
comp m1 m2 = if cod m1 == dom m2 then composeMorphisms m1 m2 else
  fail "target of first and source of second morphism are different"

instance Ord sign => Category sign (DefaultMorphism sign) where
    dom = domOfDefaultMorphism
    cod = codOfDefaultMorphism
    ide = ideOfDefaultMorphism
    isInclusion = const True
    composeMorphisms = compOfDefaultMorphism
    legal_mor = legalDefaultMorphism (const True)

{- | Abstract syntax, parsing and printing.
     There are three types for abstract syntax:
     basic_spec is for basic specifications (see CASL RefMan p. 5ff.),
     symb_items is for symbol lists (see CASL RefMan p. 35ff.),
     symb_map_items is for symbol maps (see CASL RefMan p. 35ff.).
-}
class (Language lid, PrintTypeConv basic_spec,
       EqPrintTypeConv symb_items,
       EqPrintTypeConv symb_map_items)
    => Syntax lid basic_spec symb_items symb_map_items
        | lid -> basic_spec symb_items symb_map_items
      where
         -- | parser for basic specifications
         parse_basic_spec :: lid -> Maybe(AParser st basic_spec)
         -- | parser for symbol lists
         parse_symb_items :: lid -> Maybe(AParser st symb_items)
         -- | parser for symbol maps
         parse_symb_map_items :: lid -> Maybe(AParser st symb_map_items)
         toItem :: lid -> basic_spec -> Item
         -- default implementations
         parse_basic_spec _ = Nothing
         parse_symb_items _ = Nothing
         parse_symb_map_items _ = Nothing
         toItem l _ = error $ statErrMsg l "toItem"

{- | Sentences, provers and symbols.
     Provers capture the entailment relation between sets of sentences
     and sentences. They may return proof trees witnessing proofs.
     Signatures are equipped with underlying sets of symbols
     (such that the category of signatures becomes a concrete category),
     see CASL RefMan p. 191ff.
-}
class (Language lid, Category sign morphism, Ord sentence,
       Ord symbol, --  for efficient lookup
       PrintTypeConv sign, PrintTypeConv morphism,
       PrintTypeConv sentence, PrintTypeConv symbol)
    => Sentences lid sentence sign morphism symbol
        | lid -> sentence sign morphism symbol
      where

      ----------------------- sentences ---------------------------
      -- | check whether a sentence belongs to a signature
      is_of_sign :: lid -> sentence -> sign -> Bool
      is_of_sign l _ _ = error $ statErrMsg l "is_of_sign"
      -- | sentence translation along a signature morphism
      map_sen :: lid -> morphism -> sentence -> Result sentence
      map_sen l _ _ = statErr l "map_sen"
      -- | simplification of sentences (leave out qualifications)
      simplify_sen :: lid -> sign -> sentence -> sentence
      simplify_sen _ _ = id  -- default implementation
      -- | parsing of sentences
      parse_sentence :: lid -> Maybe (AParser st sentence)
      parse_sentence _ = Nothing
      print_sign :: lid -> sign -> Doc
      print_sign _ = pretty
      -- | print a sentence with comments
      print_named :: lid -> Named sentence -> Doc
      print_named _ = printAnnoted (addBullet . pretty) . fromLabelledSen

      ----------------------- symbols ---------------------------
      -- | set of symbols for a signature
      sym_of :: lid -> sign -> Set.Set symbol
      sym_of l _ =  error $ statErrMsg l "sym_of"
      -- | symbol map for a signature morphism
      symmap_of :: lid -> morphism -> EndoMap symbol
      symmap_of l _ = error $ statErrMsg l "symmap_of"
      -- | symbols have a name, see CASL RefMan p. 192
      sym_name :: lid -> symbol -> Id
      sym_name l _ = error $ statErrMsg l "sym_name"

-- | a dummy static analysis function to allow type checking *.inline.hs files
inlineAxioms :: StaticAnalysis lid
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol => lid -> String -> [Named sentence]
inlineAxioms _ _ = error "inlineAxioms"

-- | fail function for static analysis
statErr :: (Language lid, Monad m) => lid -> String -> m a
statErr lid = fail . statErrMsg lid

-- | error message for static analysis
statErrMsg :: (Language lid) => lid -> String -> String
statErrMsg lid str = "Logic." ++ str ++ " nyi for: " ++ language_name lid

{- static analysis
   This type class provides the data needed for an institution with symbols,
   as explained in the structured specification semantics in the CASL
   reference manual, chapter III.4.
   The static analysis computes signatures from basic specifications,
   and signature morphisms from symbol lists and symbol maps. The latter
   needs an intermediate stage, so-called raw symbols, which are possibly
   unqualified symbols. Normal symbols are always fully qualified.
   In the CASL reference manual, our symbols are called "signature symbols",
   and our raw symbols are called "symbols". (Terminology should be adapted.)
-}
class ( Syntax lid basic_spec symb_items symb_map_items
      , Sentences lid sentence sign morphism symbol
      , GetRange raw_symbol, Ord raw_symbol, Pretty raw_symbol
      , Typeable raw_symbol)
    => StaticAnalysis lid
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol
        | lid -> basic_spec sentence symb_items symb_map_items
                 sign morphism symbol raw_symbol
      where
         ----------------------- static analysis ---------------------------
         {- | static analysis of basic specifications and symbol maps.
            The resulting bspec has analyzed axioms in it.
            The resulting sign is an extension of the input sign
            plus newly declared or redeclared symbols.
            See CASL RefMan p. 138 ff. -}
         basic_analysis :: lid ->
                           Maybe((basic_spec,  -- abstract syntax tree
                            sign, -- input signature, for the local
                                  -- environment, carrying the previously
                                  -- declared symbols
                            GlobalAnnos) ->   -- global annotations
                           Result (basic_spec, ExtSign sign symbol
                                  , [Named sentence]))
         -- default implementation
         basic_analysis _ = Nothing
         -- | static analysis of symbol maps, see CASL RefMan p. 222f.
         stat_symb_map_items ::
             lid -> [symb_map_items] -> Result (EndoMap raw_symbol)
         stat_symb_map_items l _ = statErr l "stat_symb_map_items"
         -- | static analysis of symbol lists, see CASL RefMan p. 221f.
         stat_symb_items :: lid -> [symb_items] -> Result [raw_symbol]
         stat_symb_items l _ = statErr l "stat_symb_items"

         ------------------------- amalgamation ---------------------------
         {- | Computation of colimits of signature diagram.
            Indeed, it suffices to compute a coconce that is weakly amalgamable
            see Till Mossakowski,
            Heterogeneous specification and the heterogeneous tool set
            p. 25ff. -}
         -- | architectural sharing analysis, see CASL RefMan p. 247ff.
         ensures_amalgamability :: lid ->
              ([CASLAmalgOpt],        -- the program options
               Gr sign (Int,morphism), -- the diagram to be analyzed
               [(Int, morphism)],     -- the sink
               Gr String String) -- the descriptions of nodes and edges
                  -> Result Amalgamates
         ensures_amalgamability l _ = warning Amalgamates
           ("amalgamability test not implemented for logic " ++ show l)
           nullRange
         -- | signature colimits
         signature_colimit :: lid -> Gr sign (Int, morphism)
                           -> Result (sign, Map.Map Int morphism)
         signature_colimit l _ = statErr l "signature_colimit"
         {- | rename and qualify the symbols considering a united incoming
            morphisms, code out overloading and
            create sentences for the overloading relation -}
         qualify :: lid -> SIMPLE_ID -> LIB_ID -> morphism -> sign
                 -> Result (morphism, [Named sentence])
         qualify l _ _ _ _ = statErr l "qualify"
         -------------------- symbols and raw symbols ---------------------
         {- | Construe a symbol, like f:->t, as a raw symbol.
            This is a one-sided inverse to the function SymSySigSym
            in the CASL RefMan p. 192. -}
         symbol_to_raw :: lid -> symbol -> raw_symbol
         symbol_to_raw l _ = error $ statErrMsg l "symbol_to_raw"
         {- | Construe an identifier, like f, as a raw symbol.
            See CASL RefMan p. 192, function IDAsSym -}
         id_to_raw :: lid -> Id -> raw_symbol
         id_to_raw l _ = error $ statErrMsg l "id_to_raw"
         {- | Check wether a symbol matches a raw symbol, for
            example, f:s->t matches f. See CASL RefMan p. 192 -}
         matches :: lid -> symbol -> raw_symbol -> Bool
         matches l _ _ = error $ statErrMsg l "matches"
         --------------- operations on signatures and morphisms -----------
         -- | the empty (initial) signature, see CASL RefMan p. 193
         empty_signature :: lid -> sign
         -- | union of signatures, see CASL RefMan p. 193
         signature_union :: lid -> sign -> sign -> Result sign
         signature_union l _ _ = statErr l "signature_union"
         -- | intersection of signatures
         intersection :: lid -> sign -> sign -> Result sign
         intersection l _ _ = statErr l "intersection"
         -- | final union of signatures, see CASL RefMan p. 194
         final_union :: lid -> sign -> sign -> Result sign
         final_union l _ _ = statErr l "final_union"
         -- | union of signature morphims, see CASL RefMan p. 196
         morphism_union :: lid -> morphism -> morphism -> Result morphism
         morphism_union l _ _ = statErr l "morphism_union"
         -- | subsignatures, see CASL RefMan p. 194
         is_subsig :: lid -> sign -> sign -> Bool
         is_subsig _ _ _ = False
         {- | construct the inclusion morphisms between subsignatures,
              see CASL RefMan p. 194 -}
         subsig_inclusion :: lid -> sign -> sign -> Result morphism
         subsig_inclusion l _ _ = statErr l "subsig_inclusion"
         {- | the signature (co)generated by a set of symbols in another
            signature is the smallest (largest) signature containing
            (excluding) the set of symbols. Needed for revealing and
            hiding, see CASL RefMan p. 197ff. -}
         generated_sign, cogenerated_sign ::
             lid -> Set.Set symbol -> sign -> Result morphism
         generated_sign l _ _ = statErr l "generated_sign"
         cogenerated_sign l _ _ = statErr l "cogenerated_sign"
         {- | Induce a signature morphism from a source signature and
            a raw symbol map. Needed for translation (SP with SM).
            See CASL RefMan p. 198 -}
         induced_from_morphism ::
             lid -> EndoMap raw_symbol -> sign -> Result morphism
         induced_from_morphism l _ _ = statErr l "induced_from_morphism"
         {- | Induce a signature morphism between two signatures by a
            raw symbol map. Needed for instantiation and views.
            See CASL RefMan p. 198f. -}
         induced_from_to_morphism ::
             lid -> EndoMap raw_symbol -> ExtSign sign symbol
                 -> ExtSign sign symbol -> Result morphism
         induced_from_to_morphism l _ _ _ =
             statErr l "induced_from_to_morphism"
         {- | Check whether a signature morphism is transportable.
            See CASL RefMan p. 304f. -}
         is_transportable :: lid -> morphism -> Bool
         is_transportable _ _ = False -- safe default
         {- | Check whether the underlying symbol map of a signature morphism
            is injective -}
         is_injective :: lid -> morphism -> Bool
         is_injective _ _ = False -- safe default
         -- | generate an ontological taxonomy, if this makes sense
         theory_to_taxonomy :: lid
                            -> TaxoGraphKind
                            -> MMiSSOntology
                            -> sign -> [Named sentence]
                            -> Result MMiSSOntology
         theory_to_taxonomy l _ _ _ _ = statErr l "theory_to_taxonomy"

-- | guarded inclusion
inclusion :: StaticAnalysis lid basic_spec sentence symb_items symb_map_items
             sign morphism symbol raw_symbol
          => lid -> sign -> sign ->  Result morphism
inclusion lid s1 s2 = if is_subsig lid s1 s2 then subsig_inclusion lid s1 s2
  else fail $ "Attempt to construct inclusion between non-subsignatures:\n"
           ++ showDoc (Set.difference (sym_of lid s1) $ sym_of lid s2) ""

{- | semi lattices with top (needed for sublogics). Note that `Ord` is
only used for efficiency and is not related to the /partial/ order given
by the lattice. Only `Eq` is used to define `isSubElem` -}
class (Ord l, Show l) => SemiLatticeWithTop l where
  join :: l -> l -> l
  top :: l

instance SemiLatticeWithTop () where
  join _ _ = ()
  top = ()

-- | less or equal for semi lattices
isSubElem :: SemiLatticeWithTop l => l -> l -> Bool
isSubElem a b = join a b == b

-- | class providing the minimal sublogic of an item
class MinSublogic sublogic item where
    minSublogic :: item -> sublogic

-- | a default instance for no sublogics
instance MinSublogic () a where
    minSublogic _ = ()

-- | class providing also the projection of an item to a sublogic
class MinSublogic sublogic item => ProjectSublogic sublogic item where
    projectSublogic :: sublogic -> item -> item

-- | a default instance for no sublogics
instance ProjectSublogic () b where
    projectSublogic _ = id

-- | like ProjectSublogic, but providing a partial projection
class MinSublogic sublogic item => ProjectSublogicM sublogic item where
    projectSublogicM :: sublogic -> item -> Maybe item

-- | a default instance for no sublogics
instance ProjectSublogicM () b where
    projectSublogicM _ = Just

-- | a class for providing a sublogi name
class SublogicName l where
    sublogicName :: l -> String

instance SublogicName () where
    sublogicName () = ""

{- Type class logic. The central type class of Hets, providing the
   interface for logics. This type class is instantiated for many logics,
   and it is used for the logic independent parts of Hets.
   It hence provides an abstraction barrier between logic specific and
   logic indepdendent code.
   This type class extends the class StaticAnalysis by a sublogic mechanism.
   Sublogics are important since they avoid the need to provide an own
   instance of the class logic for each sublogic. Instead, the sublogic
   can use the datastructures and operations of the main logic, and
   functions are provided to test whether a given item lies within the
   sublogic. Also, projection functions from a super-logic to a sublogic
   are provided.
-}
class (StaticAnalysis lid
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol,
       SemiLatticeWithTop sublogics,
       MinSublogic sublogics sentence,
       ProjectSublogic sublogics basic_spec,
       ProjectSublogicM sublogics symb_items,
       ProjectSublogicM sublogics symb_map_items,
       ProjectSublogic sublogics sign,
       ProjectSublogic sublogics morphism,
       ProjectSublogicM sublogics symbol,
       Convertible sublogics,
       SublogicName sublogics,
       Ord proof_tree, Show proof_tree,
       Convertible proof_tree)
    => Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        | lid -> sublogics
                 basic_spec sentence symb_items symb_map_items
                 sign morphism symbol raw_symbol proof_tree
          where

         -- | stability of the implementation
         stability :: lid -> Stability
         -- default
         stability _ = Experimental

         -- | for a process logic, return its data logic
         data_logic :: lid -> Maybe AnyLogic
         data_logic _ = Nothing

         -- | the top sublogic, corresponding to the whole logic
         top_sublogic :: lid -> sublogics
         top_sublogic _ = top

         -- | list all the sublogics of the current logic
         all_sublogics :: lid -> [sublogics]
         all_sublogics li = [top_sublogic li]

         {- | provide the embedding of a projected signature into the
              original signature -}
         proj_sublogic_epsilon :: lid -> sublogics -> sign -> morphism
         proj_sublogic_epsilon _ _ s = ide s

         ----------------------- provers ---------------------------
         -- | several provers can be provided. See module "Logic.Prover"
         provers :: lid -> [Prover sign sentence morphism sublogics proof_tree]
         provers _ = [] -- default implementation
         -- | consistency checkers
         cons_checkers :: lid
                       -> [ConsChecker sign sentence
                                       sublogics morphism proof_tree]
         cons_checkers _ = [] -- default implementation
         -- | conservativity checkers
         conservativityCheck :: lid
                             -> [ConservativityChecker sign sentence morphism]
         conservativityCheck _ = []
         -- | the empty proof tree
         empty_proof_tree :: lid -> proof_tree
         empty_proof_tree l = error $ statErrMsg l "empty_proof_tree"

         ----------------------- OMDoc ---------------------------
         export_signToOmdoc :: lid -> SIMPLE_ID -> LIB_ID -> sign
                           -> [OMDoc.TCElement]
         -- default implementation
         export_signToOmdoc lid _ _ _ =
             error $ "export_signToOmdoc not yet implemented "
                       ++ "for logic " ++ (show lid)

         export_morphismToOmdoc :: lid -> morphism -> OMDoc.TCElement
         -- default implementation
         export_morphismToOmdoc lid _ =
             error $ "export_morphismToOmdoc not yet implemented "
                       ++ "for logic " ++ (show lid)

         export_senToOmdoc :: lid -> SIMPLE_ID -> LIB_ID -> sign
                          -> Named sentence -> OMDoc.TCElement
         -- default implementation
         export_senToOmdoc lid _ _ _ _  =
             error $ "export_senToOmdoc not yet implemented "
                       ++ "for logic " ++ (show lid)

         omdoc_metatheory :: lid -> Maybe OMDoc.OMCD
         -- default implementation
         omdoc_metatheory _lid = Nothing

----------------------------------------------------------------
-- Derived functions
----------------------------------------------------------------

-- | the empty theory
empty_theory :: StaticAnalysis lid
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol =>
        lid -> Theory sign sentence proof_tree
empty_theory lid = Theory (empty_signature lid) Map.empty

----------------------------------------------------------------
-- Existential type covering any logic
----------------------------------------------------------------

-- | the disjoint union of all logics
data AnyLogic = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree =>
        Logic lid
  deriving Typeable

instance GetRange AnyLogic

instance Show AnyLogic where
  show (Logic lid) = language_name lid
instance Eq AnyLogic where
  Logic lid1 == Logic lid2 = language_name lid1 == language_name lid2

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
