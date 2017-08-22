{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, DeriveDataTypeable
  , FlexibleInstances, UndecidableInstances, ExistentialQuantification #-}
{- |
Module      :  ./Logic/Logic.hs
Description :  central interface (type class) for logics in Hets
Copyright   :  (c) Till Mossakowski, and Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt
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

import Logic.Prover (Prover, ConsChecker, Theory (..))
import Logic.KnownIris

import Taxonomy.MMiSSOntology (MMiSSOntology)

import ATC.DefaultMorphism ()

import qualified OMDoc.DataTypes as OMDoc
  ( TCElement
  , TCorOMElement
  , NameMap
  , SigMap
  , SigMapI
  , OMCD
  , OmdADT)

import ATerm.Lib (ShATermConvertible)

import Common.AS_Annotation
import Common.Amalgamate
import Common.AnnoState
import Common.Consistency
import Common.DefaultMorphism
import Common.Doc
import Common.DocUtils
import Common.ExtSign
import Common.GlobalAnnotations
import Common.Id
import Common.IRI
import Common.Item
import Common.Json
import Common.Lib.Graph
import Common.LibName
import Common.Prec (PrecMap)
import Common.Result
import Common.Taxonomy
import Common.ToXml

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Monoid
import Data.Ord
import Data.Typeable
import Control.Monad (unless)

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
     Define instances like "data CASL = CASL deriving (Show, Typeable, Data)"
-}
class Show lid => Language lid where
    language_name :: lid -> String
    language_name = show
    description :: lid -> String
    -- default implementation
    description _ = ""

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
         {- | composition, in diagrammatic order,
         if intermediate objects are equal (not checked!) -}
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
         legal_mor :: morphism -> Result ()
         legal_mor _ = return ()

-- | test if the signature morphism is the identity
isIdentity :: Category object morphism => morphism -> Bool
isIdentity m = isInclusion m && dom m == cod m

comp :: Category object morphism => morphism -> morphism -> Result morphism
comp m1 m2 = if cod m1 == dom m2 then composeMorphisms m1 m2 else
  fail "target of first and source of second morphism are different"

instance Ord sign => Category sign (DefaultMorphism sign) where
    dom = domOfDefaultMorphism
    cod = codOfDefaultMorphism
    ide = ideOfDefaultMorphism
    isInclusion = const True
    composeMorphisms = compOfDefaultMorphism

{- | Abstract syntax, parsing and printing.
     There are three types for abstract syntax:
     basic_spec is for basic specifications (see CASL RefMan p. 5ff.),
     symb_items is for symbol lists (see CASL RefMan p. 35ff.),
     symb_map_items is for symbol maps (see CASL RefMan p. 35ff.).
-}
class (Language lid, PrintTypeConv basic_spec, GetRange basic_spec,
       Monoid basic_spec, -- for joining converted signatures and sentences
       Pretty symbol,
       EqPrintTypeConv symb_items,
       EqPrintTypeConv symb_map_items)
    => Syntax lid basic_spec symbol symb_items symb_map_items
        | lid -> basic_spec symbol symb_items symb_map_items
      where
         -- | parsers and printers
         parsersAndPrinters :: lid -> Map.Map String
            (PrefixMap -> AParser st basic_spec, basic_spec -> Doc)
         parsersAndPrinters li = case parse_basic_spec li of
            Nothing -> Map.empty
            Just p -> makeDefault (p, pretty)
         -- | parser for basic specifications
         parse_basic_spec :: lid -> Maybe (PrefixMap -> AParser st basic_spec)
         -- | parser for a single symbol returned as list
         parseSingleSymbItem :: lid -> Maybe (AParser st symb_items)
         -- | parser for symbol lists
         parse_symb_items :: lid -> Maybe (AParser st symb_items)
         -- | parser for symbol maps
         parse_symb_map_items :: lid -> Maybe (AParser st symb_map_items)
         toItem :: lid -> basic_spec -> Item
         symb_items_name :: lid -> symb_items -> [String]
         -- default implementations
         parse_basic_spec _ = Nothing
         parseSingleSymbItem _ = Nothing
         parse_symb_items _ = Nothing
         parse_symb_map_items _ = Nothing
         symb_items_name _ _ = [""]
         toItem _ bs = mkFlatItem ("Basicspec", pretty bs) $ getRangeSpan bs

basicSpecParser :: Syntax lid basic_spec symbol symb_items symb_map_items
  => Maybe IRI -> lid -> Maybe (PrefixMap -> AParser st basic_spec)
basicSpecParser sm = fmap fst . parserAndPrinter sm

basicSpecPrinter :: Syntax lid basic_spec symbol symb_items symb_map_items
  => Maybe IRI -> lid -> Maybe (basic_spec -> Doc)
basicSpecPrinter sm = fmap snd . parserAndPrinter sm

basicSpecSyntaxes :: Syntax lid basic_spec symbol symb_items symb_map_items
  => lid -> [String]
basicSpecSyntaxes = Map.keys . serializations . language_name

parserAndPrinter :: Syntax lid basic_spec symbol symb_items symb_map_items
  => Maybe IRI -> lid -> Maybe (PrefixMap -> AParser st basic_spec,
                                basic_spec -> Doc)
parserAndPrinter sm l = lookupDefault l sm (parsersAndPrinters l)

-- | function to lookup parser or printer
lookupDefault :: Syntax lid basic_spec symbol symb_items symb_map_items
  => lid -> Maybe IRI -> Map.Map String b -> Maybe b
lookupDefault l im m = case im of
     Just i -> do
       let s = iriToStringUnsecure i
       ser <- if isSimple i then return s
              else lookupSerialization (language_name l) s
       Map.lookup ser m
     Nothing -> if Map.size m == 1 then Just $ head $ Map.elems m
                else Map.lookup "" m

showSyntax :: Language lid => lid -> Maybe IRI -> String
showSyntax lid = (("logic " ++ language_name lid) ++)
   . maybe "" ((" serialization " ++) . iriToStringUnsecure)

makeDefault :: b -> Map.Map String b
makeDefault = Map.singleton ""

addSyntax :: String -> b -> Map.Map String b -> Map.Map String b
addSyntax = Map.insert

{- | Sentences, provers and symbols.
     Provers capture the entailment relation between sets of sentences
     and sentences. They may return proof trees witnessing proofs.
     Signatures are equipped with underlying sets of symbols
     (such that the category of signatures becomes a concrete category),
     see CASL RefMan p. 191ff.
-}
class (Language lid, Category sign morphism, Ord sentence,
       Ord symbol, -- for efficient lookup
       PrintTypeConv sign, PrintTypeConv morphism,
       GetRange sentence, GetRange symbol,
       PrintTypeConv sentence, ToJson sentence,
       ToXml sentence, PrintTypeConv symbol)
    => Sentences lid sentence sign morphism symbol
        | lid -> sentence sign morphism symbol
      where

      -- | sentence translation along a signature morphism
      map_sen :: lid -> morphism -> sentence -> Result sentence
      map_sen l _ _ = statFail l "map_sen"

      -- | simplification of sentences (leave out qualifications)
      simplify_sen :: lid -> sign -> sentence -> sentence
      simplify_sen _ _ = id

      -- | negation of a sentence for disproving
      negation :: lid -> sentence -> Maybe sentence
      negation _ _ = Nothing

      -- | modified signature printing when followed by sentences
      print_sign :: lid -> sign -> Doc
      print_sign _ = pretty

      -- | print a sentence with comments
      print_named :: lid -> Named sentence -> Doc
      print_named _ = printAnnoted (addBullet . pretty) . fromLabelledSen

      -- --------------------- symbols ---------------------------

      -- | dependency ordered list of symbol sets for a signature
      sym_of :: lid -> sign -> [Set.Set symbol]
      sym_of _ _ = []
      {- | Dependency ordered list of a bigger symbol set for a
      signature. This function contains more symbols than those being subject
      to hiding and renaming (given by 'sym_of') to better represent a
      signature as a set of symbols given within xml files. At least for CASL
      additional symbols for (direct) subsorts will be created, but note, that
      no symbol for a partial function will be created, if the signature
      contains this function as total, although a signature with just that
      partial function would be a subsignature. This function is supposed to
      work over partial signatures created by 'signatureDiff'. -}
      mostSymsOf :: lid -> sign -> [symbol]
      mostSymsOf l = concatMap Set.toList . sym_of l

      -- | symbol map for a signature morphism
      symmap_of :: lid -> morphism -> EndoMap symbol
      symmap_of _ _ = Map.empty
      -- | symbols have a name, see CASL RefMan p. 192
      sym_name :: lid -> symbol -> Id
      sym_name l _ = statError l "sym_name"
      -- | some symbols have a label for better readability
      sym_label :: lid -> symbol -> Maybe String
      sym_label _ _ = Nothing
      -- | the fully qualified name for XML output (i.e. of OWL2)
      fullSymName :: lid -> symbol -> String
      fullSymName l = show . sym_name l
      -- | a logic dependent kind of a symbol
      symKind :: lid -> symbol -> String
      symKind _ _ = ""
      -- | the symbols occuring in a sentence (any order)
      symsOfSen :: lid -> sign -> sentence -> [symbol]
      symsOfSen _ _ _ = []
      -- | combine two symbols into another one
      pair_symbols :: lid -> symbol -> symbol -> Result symbol
      pair_symbols lid _ _ = error $ "pair_symbols nyi for logic " ++ show lid

-- | makes a singleton list from the given value
singletonList :: a -> [a]
singletonList x = [x]

-- | set of symbols for a signature
symset_of :: forall lid sentence sign morphism symbol .
             Sentences lid sentence sign morphism symbol =>
             lid -> sign -> Set.Set symbol
symset_of lid sig = Set.unions $ sym_of lid sig

-- | dependency ordered list of symbols for a signature
symlist_of :: forall lid sentence sign morphism symbol .
              Sentences lid sentence sign morphism symbol =>
              lid -> sign -> [symbol]
symlist_of lid sig = concatMap Set.toList $ sym_of lid sig

-- | a dummy static analysis function to allow type checking *.inline.hs files
inlineAxioms :: StaticAnalysis lid
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol => lid -> String -> [Named sentence]
inlineAxioms _ _ = error "inlineAxioms"

-- | fail function for static analysis
statFail :: (Language lid, Monad m) => lid -> String -> m a
statFail lid = fail . statErrMsg lid

statError :: Language lid => lid -> String -> a
statError lid = error . statErrMsg lid

-- | error message for static analysis
statErrMsg :: Language lid => lid -> String -> String
statErrMsg lid str =
  "Logic." ++ str ++ " not implemented for: " ++ language_name lid

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

data REL_REF = Subs | IsSubs | Equiv | Incomp
                  | HasInst | InstOf | DefRel
                  | RelName IRI
                    deriving (Show, Eq)

class ( Syntax lid basic_spec symbol symb_items symb_map_items
      , Sentences lid sentence sign morphism symbol
      , GetRange raw_symbol, Ord raw_symbol, Pretty raw_symbol
      , Typeable raw_symbol)
    => StaticAnalysis lid
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol
        | lid -> basic_spec sentence symb_items symb_map_items
                 sign morphism symbol raw_symbol
      where
         {- | static analysis of basic specifications and symbol maps.
            The resulting bspec has analyzed axioms in it.
            The resulting sign is an extension of the input sign
            plus newly declared or redeclared symbols.
            See CASL RefMan p. 138 ff. -}
         basic_analysis :: lid
           -> Maybe ((basic_spec, sign, GlobalAnnos)
             -> Result (basic_spec, ExtSign sign symbol, [Named sentence]))
         basic_analysis _ = Nothing
         -- | Analysis of just sentences
         sen_analysis :: lid
           -> Maybe ((basic_spec, sign, sentence) -> Result sentence)
         sen_analysis _ = Nothing
         -- | a basic analysis with additional arguments
         extBasicAnalysis :: lid -> IRI -> LibName
             -> basic_spec -> sign -> GlobalAnnos
             -> Result (basic_spec, ExtSign sign symbol, [Named sentence])
         extBasicAnalysis l _ _ b s g = case basic_analysis l of
            Nothing -> statFail l "basic_analysis"
            Just ba -> ba (b, s, g)
         -- | static analysis of symbol maps, see CASL RefMan p. 222f.
         stat_symb_map_items :: lid -> sign -> Maybe sign -> [symb_map_items]
             -> Result (EndoMap raw_symbol)
         stat_symb_map_items l _ _ _ = statFail l "stat_symb_map_items"
         -- | static analysis of symbol lists, see CASL RefMan p. 221f.
         stat_symb_items :: lid -> sign -> [symb_items] -> Result [raw_symbol]
         stat_symb_items l _ _ = statFail l "stat_symb_items"

         -- | convert a theory to basic specs for different serializations
         convertTheory :: lid -> Maybe ((sign, [Named sentence]) -> basic_spec)
         convertTheory _ = Nothing

         {- ----------------------- amalgamation ---------------------------
            Computation of colimits of signature diagram.
            Indeed, it suffices to compute a cocone that is weakly amalgamable
            see Till Mossakowski,
            Heterogeneous specification and the heterogeneous tool set
            p. 25ff. -}

         -- | architectural sharing analysis, see CASL RefMan p. 247ff.
         ensures_amalgamability :: lid ->
              ([CASLAmalgOpt],        -- the program options
               Gr sign (Int, morphism), -- the diagram to be analyzed
               [(Int, morphism)],     -- the sink
               Gr String String) -- the descriptions of nodes and edges
                  -> Result Amalgamates
         ensures_amalgamability l _ = warning Amalgamates
           ("amalgamability test not implemented for logic " ++ show l)
           nullRange
         -- | quotient term algebra for normalization of freeness
         quotient_term_algebra :: lid -- the logic
             -> morphism -- sigma : Sigma -> SigmaM
             -> [Named sentence] -- Th(M)
             -> Result
                 (sign, -- SigmaK
                  [Named sentence] -- Ax(K)
                 )
         quotient_term_algebra l _ _ = statFail l "quotient_term_algebra"
         -- | signature colimits
         signature_colimit :: lid -> Gr sign (Int, morphism)
                           -> Result (sign, Map.Map Int morphism)
         signature_colimit l _ = statFail l "signature_colimit"
         {- | rename and qualify the symbols considering a united incoming
            morphisms, code out overloading and
            create sentences for the overloading relation -}
         qualify :: lid -> SIMPLE_ID -> LibName -> morphism -> sign
                 -> Result (morphism, [Named sentence])
         qualify l _ _ _ _ = statFail l "qualify"

         -- ------------------ symbols and raw symbols ---------------------

         {- | Construe a symbol, like f:->t, as a raw symbol.
            This is a one-sided inverse to the function SymSySigSym
            in the CASL RefMan p. 192. -}
         symbol_to_raw :: lid -> symbol -> raw_symbol
         symbol_to_raw l _ = statError l "symbol_to_raw"
         {- | Construe an identifier, like f, as a raw symbol.
            See CASL RefMan p. 192, function IDAsSym -}
         id_to_raw :: lid -> Id -> raw_symbol
         id_to_raw l _ = statError l "id_to_raw"
         {- | Check whether a symbol matches a raw symbol, for
            example, f:s->t matches f. See CASL RefMan p. 192 -}
         matches :: lid -> symbol -> raw_symbol -> Bool
         matches _ _ _ = True

         -- ------------- operations on signatures and morphisms -----------

         -- | the empty (initial) signature, see CASL RefMan p. 193
         empty_signature :: lid -> sign
         -- | adds a symbol to a given signature
         add_symb_to_sign :: lid -> sign -> symbol -> Result sign
         add_symb_to_sign l _ _ = statFail l "add_symb_to_sign"
         -- | union of signatures, see CASL RefMan p. 193
         signature_union :: lid -> sign -> sign -> Result sign
         signature_union l _ _ = statFail l "signature_union"

         -- | difference of signatures resulting in unclosed pre-signatures
         signatureDiff :: lid -> sign -> sign -> Result sign
         signatureDiff l _ _ = statFail l "signatureDiff"

         -- | intersection of signatures
         intersection :: lid -> sign -> sign -> Result sign
         intersection l _ _ = statFail l "intersection"
         -- | final union of signatures, see CASL RefMan p. 194
         final_union :: lid -> sign -> sign -> Result sign
         final_union l _ _ = statFail l "final_union"
         -- | union of signature morphims, see CASL RefMan p. 196
         morphism_union :: lid -> morphism -> morphism -> Result morphism
         morphism_union l _ _ = statFail l "morphism_union"
         -- | subsignatures, see CASL RefMan p. 194
         is_subsig :: lid -> sign -> sign -> Bool
         is_subsig _ _ _ = False
         {- | construct the inclusion morphisms between subsignatures,
              see CASL RefMan p. 194 -}
         subsig_inclusion :: lid -> sign -> sign -> Result morphism
         subsig_inclusion l _ _ = statFail l "subsig_inclusion"
         {- | the signature (co)generated by a set of symbols in another
            signature is the smallest (largest) signature containing
            (excluding) the set of symbols. Needed for revealing and
            hiding, see CASL RefMan p. 197ff. -}
         generated_sign, cogenerated_sign ::
             lid -> Set.Set symbol -> sign -> Result morphism
         generated_sign l _ _ = statFail l "generated_sign"
         cogenerated_sign l _ _ = statFail l "cogenerated_sign"
         {- | Induce a signature morphism from a source signature and
            a raw symbol map. Needed for translation (SP with SM).
            See CASL RefMan p. 198 -}
         induced_from_morphism ::
             lid -> EndoMap raw_symbol -> sign -> Result morphism
         induced_from_morphism l _ _ = statFail l "induced_from_morphism"
         {- | Induce a signature morphism between two signatures by a
            raw symbol map. Needed for instantiation and views.
            See CASL RefMan p. 198f. -}
         induced_from_to_morphism ::
             lid -> EndoMap raw_symbol -> ExtSign sign symbol
                 -> ExtSign sign symbol -> Result morphism
         induced_from_to_morphism l rm (ExtSign sig _) (ExtSign tar _) = do
           mor <- induced_from_morphism l rm sig
           inclusion l (cod mor) tar >>= composeMorphisms mor
         {- | Check whether a signature morphism is transportable.
            See CASL RefMan p. 304f. -}
         is_transportable :: lid -> morphism -> Bool
         is_transportable _ _ = False
         {- | Check whether the underlying symbol map of a signature morphism
            is injective -}
         is_injective :: lid -> morphism -> Bool
         is_injective _ _ = False
         -- | generate an ontological taxonomy, if this makes sense
         theory_to_taxonomy :: lid
                            -> TaxoGraphKind
                            -> MMiSSOntology
                            -> sign -> [Named sentence]
                            -> Result MMiSSOntology
         theory_to_taxonomy l _ _ _ _ = statFail l "theory_to_taxonomy"
         -- | create a theory from a correspondence
         corresp2th :: lid
                    -> String -- the name of the alignment
                    -> Bool   -- flag: should we disambiguate in the bridge
                    -> sign
                    -> sign
                    -> [symb_items]
                    -> [symb_items]
                    -> EndoMap symbol
                    -> EndoMap symbol
                    -> REL_REF
                    -> Result (sign, [Named sentence], sign, sign,
                               EndoMap symbol, EndoMap symbol)
         corresp2th _ _ _ _ _ _ _ _ _ = error "c2th nyi"
         -- | create a co-span fragment from an equivalence
         equiv2cospan :: lid -> sign -> sign -> [symb_items] -> [symb_items]
           -> Result (sign, sign, sign, EndoMap symbol, EndoMap symbol)
         equiv2cospan _ _ _ _ _ = error "equiv2cospan nyi"
         -- | extract the module
         extract_module :: lid -> [IRI] -> (sign, [Named sentence])
                        -> Result (sign, [Named sentence])
         extract_module _ _ = return

-- | print a whole theory
printTheory :: StaticAnalysis lid basic_spec sentence symb_items symb_map_items
               sign morphism symbol raw_symbol
  => Maybe IRI -> lid -> (sign, [Named sentence]) -> Doc
printTheory sm lid th@(s, l) = case
           (convertTheory lid, basicSpecPrinter sm lid) of
             (Just c, Just p) -> p (c th)
             _ -> print_sign lid s $++$ vsep (map (print_named lid) l)

-- | guarded inclusion
inclusion :: StaticAnalysis lid basic_spec sentence symb_items symb_map_items
             sign morphism symbol raw_symbol
          => lid -> sign -> sign -> Result morphism
inclusion l s1 s2 = if is_subsig l s1 s2 then subsig_inclusion l s1 s2
  else fail $ show $ fsep
       [ text (language_name l)
       , text "symbol(s) missing in target:"
       , pretty $ Set.difference (symset_of l s1) $ symset_of l s2 ]

{- | semi lattices with top (needed for sublogics). Note that `Ord` is
only used for efficiency and is not related to the /partial/ order given
by the lattice. Only `Eq` is used to define `isSubElem` -}
class (Ord l, Show l) => SemiLatticeWithTop l where
  lub :: l -> l -> l -- least upper bound or "join"
  top :: l

instance SemiLatticeWithTop () where
  lub _ _ = ()
  top = ()

-- | less or equal for semi lattices
isSubElem :: SemiLatticeWithTop l => l -> l -> Bool
isSubElem a b = lub a b == b

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

-- | a type for syntax information eventually stored in the signature
type SyntaxTable = (PrecMap, AssocMap)

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
         -- Parser of sentence (Added for Hybridized logics)
         parse_basic_sen :: lid -> Maybe (basic_spec -> AParser st sentence)
         parse_basic_sen _ = Nothing

         -- | stability of the implementation
         stability :: lid -> Stability
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

         {- a bottom sublogic can be extended along several dimensions
         joining all last elements of a dimension should yield the top-sublogic
         -}
         bottomSublogic :: lid -> Maybe sublogics
         bottomSublogic _ = Nothing

         sublogicDimensions :: lid -> [[sublogics]]
         sublogicDimensions li = [all_sublogics li]

         -- | parse sublogic (override more efficiently)
         parseSublogic :: lid -> String -> Maybe sublogics
         parseSublogic li s = lookup s $ map (\ l -> (sublogicName l, l))
           $ all_sublogics li

         {- | provide the embedding of a projected signature into the
              original signature -}
         proj_sublogic_epsilon :: lid -> sublogics -> sign -> morphism
         proj_sublogic_epsilon _ _ = ide

         -- --------------------- provers ---------------------------

         -- | several provers can be provided. See module "Logic.Prover"
         provers :: lid -> [Prover sign sentence morphism sublogics proof_tree]
         provers _ = []
         -- | consistency checkers
         cons_checkers :: lid
                       -> [ConsChecker sign sentence
                                       sublogics morphism proof_tree]
         cons_checkers _ = []
         -- | conservativity checkers
         conservativityCheck :: lid
                             -> [ConservativityChecker sign sentence morphism]
         conservativityCheck _ = []
         -- | the empty proof tree
         empty_proof_tree :: lid -> proof_tree
         empty_proof_tree l = statError l "empty_proof_tree"

         -- --------------------- OMDoc ---------------------------

         syntaxTable :: lid -> sign -> Maybe SyntaxTable
         syntaxTable _ _ = Nothing

         omdoc_metatheory :: lid -> Maybe OMDoc.OMCD
         {- default implementation, no logic should throw an error here
         and the base of omcd should be a parseable URI -}
         omdoc_metatheory _ = Nothing


         export_symToOmdoc :: lid -> OMDoc.NameMap symbol
                           -> symbol -> String -> Result OMDoc.TCElement
         export_symToOmdoc l _ _ = statFail l "export_symToOmdoc"

         export_senToOmdoc :: lid -> OMDoc.NameMap symbol
                          -> sentence -> Result OMDoc.TCorOMElement
         export_senToOmdoc l _ _ = statFail l "export_senToOmdoc"

         {- | additional information which has to be exported can be
         exported by this function -}
         export_theoryToOmdoc :: lid -> OMDoc.SigMap symbol -> sign
                              -> [Named sentence] -> Result [OMDoc.TCElement]
         {- default implementation does no extra export
         , sufficient in some cases -}
         export_theoryToOmdoc _ _ _ _ = return []


         omdocToSym :: lid -> OMDoc.SigMapI symbol -> OMDoc.TCElement
                    -> String -> Result symbol
         omdocToSym l _ _ _ = statFail l "omdocToSym"

         omdocToSen :: lid -> OMDoc.SigMapI symbol -> OMDoc.TCElement
                    -> String -> Result (Maybe (Named sentence))
         omdocToSen l _ _ _ = statFail l "omdocToSen"

         {- | Algebraic Data Types are imported with this function.
         By default the input is returned without changes. -}
         addOMadtToTheory :: lid -> OMDoc.SigMapI symbol
                          -> (sign, [Named sentence]) -> [[OMDoc.OmdADT]]
                          -> Result (sign, [Named sentence])
         -- no logic should throw an error here
         addOMadtToTheory l _ t adts = do
           unless (null adts) $ warning ()
                      (concat [ "ADT handling not implemented for logic "
                              , show l, " but some adts have to be handled" ])
                      nullRange
           return t

         {- | additional information which has to be imported can be
         imported by this function. By default the input is returned
         without changes. -}
         addOmdocToTheory :: lid -> OMDoc.SigMapI symbol
                          -> (sign, [Named sentence]) -> [OMDoc.TCElement]
                          -> Result (sign, [Named sentence])
         -- no logic should throw an error here
         addOmdocToTheory _ _ t _ = return t


-- | sublogic of a theory
sublogicOfTheo :: (Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree) =>
    lid -> (sign, [sentence]) -> sublogics
sublogicOfTheo _ (sig, axs) =
  foldl lub (minSublogic sig) $
  map minSublogic axs


{- The class of logics which can be used as logical frameworks, in which object
   logics can be specified by the user. Currently the only logics implementing
   this class are LF, Maude, and Isabelle, with the latter two only having
   dummy implementations.

   The function "base_sig" returns the base signature of the framework -
   for details see Integrating Logical Frameworks in Hets by M. Codescu et al
   (WADT10).

   The function "write_logic" constructs the contents of the Logic_L
   file, where L is the name of the object logic passed as an argument.
   Typically, this file will declare the lid of the object logic L and
   instances of the classes Language, Syntax, Sentences, Logic, and
   StaticAnalysis. The instance of Category is usually inherited from
   the framework itself as the object logic reuses the signatures and
   morphisms of the framework.

   The function "write_syntax" constructs the contents of the file declaring
   the Ltruth morphism (see the reference given above). If proofs and models
   are later integrated into Hets, there should be analogous functions
   "write_proofs" and "write_models" added, declaring the Lpf and
   Lmod morphisms respectively. -}
class Logic lid sublogics basic_spec sentence
            symb_items symb_map_items sign
            morphism symbol raw_symbol proof_tree
      => LogicalFramework lid sublogics basic_spec sentence
            symb_items symb_map_items sign
            morphism symbol raw_symbol proof_tree
            | lid -> sublogics basic_spec sentence symb_items symb_map_items
                     sign morphism symbol raw_symbol proof_tree
      where
      -- | the base signature
      base_sig :: lid -> sign
      base_sig l = error $ "Function base_sig nyi for logic " ++ shows l "."

      {- | generation of the object logic instances
           second argument is object logic name -}
      write_logic :: lid -> String -> String
      write_logic l = error
         $ "Function write_logic nyi for logic " ++ shows l "."

      {- | generation of the Ltruth morphism declaration
           second argument is the object logic name
           third argument is the Ltruth morphism -}
      write_syntax :: lid -> String -> morphism -> String
      write_syntax l = error $
         "Function write_syntax nyi for logic " ++ shows l "."
      write_proof :: lid -> String -> morphism -> String
      write_proof l = error $
         "Function write_proof nyi for logic " ++ shows l "."
      write_model :: lid -> String -> morphism -> String
      write_model l = error $
         "Function write_model nyi for logic " ++ shows l "."
      read_morphism :: lid -> FilePath -> morphism
      read_morphism l _ = error $
         "Function read_morphism nyi for logic " ++ shows l "."

      write_comorphism :: lid -> String -> String -> String
                           -> morphism -> morphism -> morphism
                           -> String
      write_comorphism l = error $
         "Function write_comorphism nyi for logic " ++ shows l "."

{- --------------------------------------------------------------
Derived functions
-------------------------------------------------------------- -}

-- | the empty theory
emptyTheory :: StaticAnalysis lid
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol =>
        lid -> Theory sign sentence proof_tree
emptyTheory lid = Theory (empty_signature lid) Map.empty

{- --------------------------------------------------------------
Existential type covering any logic
-------------------------------------------------------------- -}

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
  a == b = compare a b == EQ

instance Ord AnyLogic where
  compare = comparing show

{- class hierarchy:
                            Language
               __________/
   Category
      |                  /
   Sentences      Syntax
      \            /
      StaticAnalysis (no sublogics)
            |
            |
           Logic
-}
