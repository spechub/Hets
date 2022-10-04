{-# LANGUAGE CPP, MultiParamTypeClasses, TypeSynonymInstances
  , FlexibleInstances #-}
{- |
Module      :  ./CASL/Logic_CASL.hs
Description :  Instance of class Logic for the CASL logic
Copyright   :  (c) Klaus Luettich, Uni Bremen 2002-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

Instance of class Logic for the CASL logic
   Also the instances for Syntax and Category.
-}

module CASL.Logic_CASL where

import ATC.ProofTree ()

import CASL.AS_Basic_CASL
import CASL.Parse_AS_Basic
import CASL.Kif
import CASL.Kif2CASL
import CASL.Fold
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
import CASL.Quantification
import qualified CASL.OMDocImport as OMI
import CASL.OMDocExport
import CASL.Freeness

-- test
import CASL.Formula (formula, primFormula)

#ifdef UNI_PACKAGE
import CASL.QuickCheck
#endif

import Common.ProofTree
import Common.Consistency
import Common.DocUtils

import Data.Monoid ()
import qualified Data.Set as Set

import Logic.Logic

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
    composeMorphisms = composeM composeMorphismExtension
    dom = msource
    cod = mtarget
    isInclusion = isInclusionMorphism isInclusionMorphismExtension
    legal_mor = legalMor

instance Semigroup (BASIC_SPEC b s f) where
    (Basic_spec l1) <> (Basic_spec l2) = Basic_spec $ l1 ++ l2
instance Monoid (BASIC_SPEC b s f) where
    mempty = Basic_spec []

-- abstract syntax, parsing (and printing)

instance Syntax CASL CASLBasicSpec
                Symbol SYMB_ITEMS SYMB_MAP_ITEMS
      where
         parsersAndPrinters CASL = addSyntax "KIF"
           (const $ fmap kif2CASL kifBasic, pretty)
           $ makeDefault (basicSpec [], pretty)
         parseSingleSymbItem CASL = Just . const $ symbItem []
         parse_symb_items CASL = Just . const $ symbItems []
         parse_symb_map_items CASL = Just . const $ symbMapItems []
         toItem CASL = bsToItem
         symb_items_name CASL = symbItemsName

-- lattices (for sublogics)

instance Lattice a => SemiLatticeWithTop (CASL_SL a) where
    lub = sublogics_max
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

instance MinSL a e => MinSublogic (CASL_SL a) (Sign f e) where
    minSublogic = sl_sign minSL

instance MinSL a e => MinSublogic (CASL_SL a) (Morphism f e m) where
    minSublogic = sl_morphism minSL

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

instance MinSL a e => ProjectSublogic (CASL_SL a) (Sign f e) where
    projectSublogic = pr_sign

instance MinSL a e => ProjectSublogic (CASL_SL a) (Morphism f e m) where
    projectSublogic = pr_morphism

instance Lattice a => ProjectSublogicM (CASL_SL a) Symbol where
    projectSublogicM = pr_symbol

-- CASL logic

instance Sentences CASL CASLFORMULA CASLSign CASLMor Symbol where
      map_sen CASL m = return . mapSen (const id) m
      negation CASL = negateFormula
      sym_of CASL = symOf
      mostSymsOf CASL = sigSymsOf
      symmap_of CASL = morphismToSymbMap
      sym_name CASL = symName
      symKind CASL = show . pretty . symbolKind . symbType
      extSymKind CASL = extSymbolKind . symbType
      symsOfSen CASL _ = Set.toList
        . foldFormula (symbolsRecord $ const Set.empty)
      simplify_sen CASL = simplifyCASLSen
      print_named CASL = printTheoryFormula
      -- test nominals
      is_nominal_sen CASL = isNominalSen 

instance StaticAnalysis CASL CASLBasicSpec CASLFORMULA
               SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol where
         basic_analysis CASL = Just basicCASLAnalysis
         sen_analysis CASL = Just cASLsen_analysis
         convertTheory CASL = Just convertCASLTheory
         stat_symb_map_items CASL = statSymbMapItems
         stat_symb_items CASL = statSymbItems
         signature_colimit CASL diag = return $ signColimit diag extCASLColimit
         quotient_term_algebra CASL = quotientTermAlgebra
         ensures_amalgamability CASL (opts, diag, sink, desc) =
             ensuresAmalgamability opts diag sink desc

         qualify CASL = qualifySig
         symbol_to_raw CASL = symbolToRaw
         raw_to_symbol CASL = rawToSymbol
         id_to_raw CASL = idToRaw
         matches CASL = CASL.Morphism.matches
         is_transportable CASL = isSortInjective
         is_injective CASL = isInjective
         raw_to_var CASL = rawToVar 

         empty_signature CASL = emptySign ()
         add_symb_to_sign CASL = addSymbToSign
         add_noms_to_sign CASL = addNomsToSign

         signature_union CASL s = return . addSig const s
         signatureDiff CASL s = return . diffSig const s
         intersection CASL s = return . interSig const s
         morphism_union CASL = plainMorphismUnion const
         final_union CASL = finalUnion const
         is_subsig CASL = isSubSig trueC
         subsig_inclusion CASL = sigInclusion ()
         cogenerated_sign CASL = cogeneratedSign ()
         generated_sign CASL = generatedSign ()
         induced_from_morphism CASL = inducedFromMorphism ()
         induced_from_to_morphism CASL = inducedFromToMorphism () trueC const
         theory_to_taxonomy CASL = convTaxo

instance Logic CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol ProofTree where
         stability CASL = Stable
         -- for Hybridization
         parse_basic_sen CASL = Just $ \ _ -> formula []
         parse_prim_formula CASL = Just $ const (primFormula [])

         proj_sublogic_epsilon CASL = pr_epsilon ()
         all_sublogics CASL = sublogics_all []
         sublogicDimensions CASL = sDims []
         parseSublogic CASL = parseSL (\ s -> Just ((), s))
         conservativityCheck CASL =
             [ConservativityChecker "CCC" (return Nothing) checkFreeType]
         empty_proof_tree CASL = emptyProofTree
         omdoc_metatheory CASL = Just caslMetaTheory
         export_senToOmdoc CASL = exportSenToOmdoc
         export_symToOmdoc CASL = exportSymToOmdoc
         export_theoryToOmdoc CASL = exportTheoryToOmdoc
         omdocToSen CASL = OMI.omdocToSen
         omdocToSym CASL = OMI.omdocToSym
         addOMadtToTheory CASL = OMI.addOMadtToTheory
         addOmdocToTheory CASL = OMI.addOmdocToTheory
         syntaxTable CASL = Just . getSyntaxTable
         constr_to_sens CASL = constrToSens
         -- helpers for hybridization
           -- for each type, its name and the file where it is defined
         sublogicsTypeName CASL = ("CASL_Sublogics","CASL.Sublogic")
         basicSpecTypeName CASL = ("CASLBasicSpec","CASL.Logic_CASL")
         sentenceTypeName CASL = ("CASLFORMULA","CASL.AS_Basic_CASL")
         symbItemsTypeName CASL = ("SYMB_ITEMS","CASL.AS_Basic_CASL")
         symbMapItemsTypeName CASL = ("SYMB_MAP_ITEMS","CASL.AS_Basic_CASL")
         signTypeName CASL = ("CASLSign","CASL.Sign")
         morphismTypeName CASL = ("CASLMor","CASL.Morphism")
         symbolTypeName CASL = ("Symbol","")
         rawSymbolTypeName CASL = ("RawSymbol","CASL.Morphism")
         proofTreeTypeName CASL = ("ProofTree","Common.ProofTree") 

#ifdef UNI_PACKAGE
         provers CASL = [quickCheckProver]
#endif
