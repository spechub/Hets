{-# LANGUAGE CPP #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for the CASL logic
Copyright   :  (c) Klaus Luettich, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

Instance of class Logic for the CASL logic
   Also the instances for Syntax and Category.
-}

module CASL.Logic_CASL where

import Common.AS_Annotation
import Common.Lexer((<<))
import Common.ProofTree
import Common.Consistency

import ATC.ProofTree ()

import Text.ParserCombinators.Parsec

import Logic.Logic

import CASL.AS_Basic_CASL
import CASL.Parse_AS_Basic
import CASL.ToDoc
import CASL.ToItem (bsToItem)
import CASL.SymbolParser
import CASL.MapSentence
import CASL.Amalgamability
import CASL.ATC_CASL ()
import CASL.Sublogic as SL
import CASL.Sign
import CASL.StaticAna
import CASL.ColimSign
import CASL.Morphism
import CASL.SymbolMapAnalysis
import CASL.Taxonomy
import CASL.Simplify
import CASL.SimplifySen
import CASL.CCC.FreeTypes
import CASL.CCC.OnePoint () -- currently unused
import CASL.Qualify
import CASL.OMDoc
#ifdef UNI_PACKAGE
import CASL.QuickCheck
#endif

import CASL.Freeness

data CASL = CASL deriving Show

instance Language CASL where
 description _ = unlines
  [ "CASL - the Common algebraic specification language"
  , "This logic is subsorted partial first-order logic"
  , "  with sort generation constraints"
  , "See the CASL User Manual, LNCS 2900, Springer Verlag"
  , "and the CASL Reference Manual, LNCS 2960, Springer Verlag"
  , "See also http://www.cofi.info/CASL.html"
  , ""
  , "Abbreviations of sublogic names indicate the following feature:"
  , "  Sub    -> with subsorting"
  , "  Sul    -> with a locally filtered subsort relation"
  , "  P      -> with partial functions"
  , "  C      -> with sort generation constraints"
  , "  eC     -> C without renamings"
  , "  sC     -> C with injective constructors"
  , "  seC    -> sC and eC"
  , "  FOL    -> first order logic"
  , "  FOAlg  -> FOL without predicates"
  , "  Horn   -> positive conditional logic"
  , "  GHorn  -> generalized Horn"
  , "  GCond  -> GHorn without predicates"
  , "  Cond   -> Horn without predicates"
  , "  Atom   -> atomic logic"
  , "  Eq     -> Atom without predicates"
  , "  =      -> with equality"
  , ""
  , "Examples:"
  , "  SubPCFOL=   -> the CASL logic itself"
  , "  FOAlg=      -> first order algebra (without predicates)"
  , "  SubPHorn=   -> the positive conditional fragement of CASL"
  , "  SubPAtom    -> the atomic subset of CASL"
  , "  SubPCAtom   -> SubPAtom with sort generation constraints"
  , "  Eq=         -> classical equational logic" ]

type CASLBasicSpec = BASIC_SPEC () () ()

trueC :: a -> b -> Bool
trueC _ _ = True

instance (Ord f, Ord e, Ord m, MorphismExtension e m) =>
    Category (Sign f e) (Morphism f e m) where
    ide sig = idMor (ideMorphismExtension $ extendedInfo sig) sig
    inverse = inverseMorphism inverseMorphismExtension
    composeMorphisms m1 =
      composeM (composeMorphismExtension $ extendedInfo $ msource m1) m1
    dom = msource
    cod = mtarget
    isInclusion = isInclusionMorphism isInclusionMorphismExtension
    legal_mor = legalMor

-- abstract syntax, parsing (and printing)

instance Syntax CASL CASLBasicSpec
                SYMB_ITEMS SYMB_MAP_ITEMS
      where
         parse_basic_spec CASL = Just $ basicSpec []
         parse_symb_items CASL = Just $ symbItems []
         parse_symb_map_items CASL = Just $ symbMapItems []
         toItem CASL = bsToItem

-- lattices (for sublogics)

instance Lattice a => SemiLatticeWithTop (CASL_SL a) where
    join = sublogics_max
    top = SL.top

class Lattice a => MinSL a f where
    minSL :: f -> CASL_SL a

instance MinSL () () where
    minSL () = bottom

class NameSL a where
    nameSL :: a -> String

instance NameSL () where
    nameSL _ = ""

class Lattice a => ProjForm a f where
    projForm :: CASL_SL a -> f -> Maybe (FORMULA f)

instance Lattice a => ProjForm a () where
    projForm _ = Just . ExtFORMULA

class (Lattice a, ProjForm a f) => ProjSigItem a s f where
    projSigItems :: CASL_SL a -> s -> (Maybe (SIG_ITEMS s f), [SORT])

instance (Lattice a, ProjForm a f) => ProjSigItem a () f where
    projSigItems _ s = (Just $ Ext_SIG_ITEMS s, [])

class (Lattice a, ProjForm a f) => ProjBasic a b s f where
    projBasicItems :: CASL_SL a -> b -> (Maybe (BASIC_ITEMS b s f), [SORT])

instance (Lattice a, ProjForm a f, ProjSigItem a s f)
    => ProjBasic a () s f where
    projBasicItems _ b = (Just $ Ext_BASIC_ITEMS b, [])

instance (NameSL a) => SublogicName (CASL_SL a) where
    sublogicName = sublogics_name nameSL

instance (MinSL a f, MinSL a s, MinSL a b) =>
    MinSublogic (CASL_SL a) (BASIC_SPEC b s f) where
    minSublogic = sl_basic_spec minSL minSL minSL

instance MinSL a f => MinSublogic (CASL_SL a) (FORMULA f) where
    minSublogic = sl_sentence minSL

instance Lattice a => MinSublogic (CASL_SL a) SYMB_ITEMS where
    minSublogic = sl_symb_items

instance Lattice a => MinSublogic (CASL_SL a) SYMB_MAP_ITEMS where
    minSublogic = sl_symb_map_items

instance Lattice a => MinSublogic (CASL_SL a) (Sign f e) where
    minSublogic = sl_sign

instance Lattice a => MinSublogic (CASL_SL a) (Morphism f e m) where
    minSublogic = sl_morphism

instance Lattice a => MinSublogic (CASL_SL a) Symbol where
    minSublogic = sl_symbol

instance (MinSL a f, MinSL a s, MinSL a b, ProjForm a f,
          ProjSigItem a s f, ProjBasic a b s f) =>
    ProjectSublogic (CASL_SL a) (BASIC_SPEC b s f) where
    projectSublogic = pr_basic_spec projBasicItems projSigItems projForm

instance Lattice a => ProjectSublogicM (CASL_SL a) SYMB_ITEMS where
    projectSublogicM = pr_symb_items

instance Lattice a => ProjectSublogicM (CASL_SL a) SYMB_MAP_ITEMS where
    projectSublogicM = pr_symb_map_items

instance Lattice a => ProjectSublogic (CASL_SL a) (Sign f e) where
    projectSublogic = pr_sign

instance Lattice a => ProjectSublogic (CASL_SL a) (Morphism f e m) where
    projectSublogic = pr_morphism

instance Lattice a => ProjectSublogicM (CASL_SL a) Symbol where
    projectSublogicM = pr_symbol

-- CASL logic

instance Sentences CASL CASLFORMULA CASLSign CASLMor Symbol where
      map_sen CASL m = return . mapSen (const id) m
      negation CASL = negateFormula
      parse_sentence CASL = Just (fmap item (aFormula [] << eof))
      sym_of CASL = symOf
      symmap_of CASL = morphismToSymbMap
      sym_name CASL = symName
      simplify_sen CASL = simplifyCASLSen
      print_named CASL = printTheoryFormula

instance StaticAnalysis CASL CASLBasicSpec CASLFORMULA
               SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol where
         basic_analysis CASL = Just basicCASLAnalysis
         stat_symb_map_items CASL = statSymbMapItems
         stat_symb_items CASL = statSymbItems
         signature_colimit CASL diag = return $ signColimit diag extCASLColimit
         quotient_term_algebra CASL = quotientTermAlgebra
         ensures_amalgamability CASL (opts, diag, sink, desc) =
             ensuresAmalgamability opts diag sink desc

         qualify CASL = qualifySig
         symbol_to_raw CASL = symbolToRaw
         id_to_raw CASL = idToRaw
         matches CASL = CASL.Morphism.matches
         is_transportable CASL = isSortInjective
         is_injective CASL = isInjective

         empty_signature CASL = emptySign ()
         signature_union CASL s = return . addSig const s
         intersection CASL s = return . interSig const s
         morphism_union CASL = morphismUnion (const id) const
         final_union CASL = finalUnion const
         is_subsig CASL = isSubSig trueC
         subsig_inclusion CASL = sigInclusion ()
         cogenerated_sign CASL = cogeneratedSign ()
         generated_sign CASL = generatedSign ()
         induced_from_morphism CASL = inducedFromMorphism ()
         induced_from_to_morphism CASL = inducedFromToMorphism () trueC const
         theory_to_taxonomy CASL = convTaxo

--       convSignOMDoc CASL = someFunctionFromOMDocFolderNowInCASLFolder

instance Logic CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol ProofTree where
         stability _ = Stable
         proj_sublogic_epsilon CASL = pr_epsilon ()
         all_sublogics _ = sublogics_all [()]
         conservativityCheck CASL  =
             [
             ConservativityChecker "CCC" checkFreeType
             ]
         empty_proof_tree CASL = emptyProofTree
         export_signToOmdoc CASL = exportSignToOmdoc
         export_morphismToOmdoc CASL = exportMorphismToOmdoc
         export_senToOmdoc CASL = exportSenToOmdoc
         omdoc_metatheory CASL = Just caslMetaTheory
#ifdef UNI_PACKAGE
         provers CASL = [quickCheckProver]
#endif
