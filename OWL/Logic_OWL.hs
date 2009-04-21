{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Description :  instance of the class Logic for OWL
Copyright   :  (c) Klaus Luettich, Heng Jiang, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Here is the place where the class Logic is instantiated for OWL.
__SROIQ__
-}

module OWL.Logic_OWL where

import Common.AS_Annotation
import Common.DefaultMorphism
import Common.Doc
import Common.DocUtils
import Common.ProofTree

import ATC.ProofTree ()

import Logic.Logic

import OWL.AS
import OWL.Parse
import OWL.Print ()
import OWL.ATC_OWL ()
import OWL.Sign
import OWL.StaticAnalysis
import OWL.Sublogic
import OWL.Morphism
import Common.Consistency
import Common.ProverTools
#ifdef UNI_PACKAGE
import OWL.ProvePellet
--import OWL.ProveFact
import OWL.Conservativity
import OWL.Taxonomy
#endif

data OWL = OWL deriving Show

instance Language OWL where
 description _ =
  "OWL DL -- Web Ontology Language Description Logic http://wwww.w3c.org/"

instance Syntax OWL OntologyFile SymbItems SymbMapItems where
    parse_basic_spec OWL = Just basicSpec
    parse_symb_items OWL = Just symbItems
    parse_symb_map_items OWL = Just symbMapItems

instance Sentences OWL Sentence Sign OWL_Morphism Entity where
    map_sen OWL = const return
    print_named OWL namedSen =
        pretty (sentence namedSen) <>
          if isAxiom namedSen then empty else space <> text "%implied"
    sym_of OWL = symOf

instance StaticAnalysis OWL OntologyFile Sentence
               SymbItems SymbMapItems
               Sign
               OWL_Morphism
               Entity RawSymb where
{- these functions are be implemented in OWL.StaticAna and OWL.Sign: -}
      basic_analysis OWL = Just basicOWLAnalysis
      stat_symb_items OWL = return . concatMap
          (\ (SymbItems m us) -> case m of
               Nothing -> map AnUri us
               Just ty -> map (ASymbol . Entity ty) us)
      empty_signature OWL = emptySign
      signature_union OWL s = return . addSign s
      final_union OWL = signature_union OWL
      is_subsig OWL = isSubSign
      subsig_inclusion OWL = defaultInclusion
      matches OWL e@(Entity _ u) r = case r of
        ASymbol s -> s == e
        AnUri s -> s == u
      cogenerated_sign OWL = cogeneratedSign
      generated_sign OWL = fail "cogenerated_sign OWL nyi"
#ifdef UNI_PACKAGE
      theory_to_taxonomy OWL = onto2Tax
#endif

{-   this function will be implemented in OWL.Taxonomy
         theory_to_taxonomy OWL = convTaxo
-}

instance Logic OWL OWL_SL OntologyFile Sentence SymbItems SymbMapItems
               Sign
               OWL_Morphism Entity RawSymb ProofTree where
    --     stability _ = Testing
    -- default implementations are fine
    -- the prover uses HTk and IO functions from uni
#ifdef UNI_PACKAGE
         provers OWL = unsafeFileCheck "pellet.sh" "PELLET_PATH" pelletProver
         cons_checkers OWL =
             unsafeFileCheck "pellet.sh" "PELLET_PATH" pelletConsChecker
         conservativityCheck OWL = [] ++
           (unsafeFileCheck "OWLLocality.jar" "HETS_OWL_TOOLS"
              (ConservativityChecker "Locality_BOTTOM_BOTTOM"
               (conserCheck "BOTTOM_BOTTOM"))) ++
           (unsafeFileCheck "OWLLocality.jar" "HETS_OWL_TOOLS"
              (ConservativityChecker "Locality_TOP_BOTTOM"
               (conserCheck "TOP_BOTTOM"))) ++
           (unsafeFileCheck "OWLLocality.jar" "HETS_OWL_TOOLS"
              (ConservativityChecker "Locality_TOP_TOP"
               (conserCheck "TOP_TOP")))
#endif

instance SemiLatticeWithTop OWL_SL where
    join = sl_max
    top = sl_top

instance SublogicName OWL_SL where
    sublogicName = sl_name

instance MinSublogic OWL_SL Sentence where
    minSublogic = sl_basic_spec

instance MinSublogic OWL_SL OWL_Morphism where
    minSublogic = sl_mor

instance ProjectSublogic OWL_SL OWL_Morphism where
    projectSublogic = pr_mor

instance MinSublogic OWL_SL Sign where
    minSublogic = sl_sig

instance ProjectSublogic OWL_SL Sign where
    projectSublogic = pr_sig

instance MinSublogic OWL_SL SymbItems where
    minSublogic _ = sl_top

instance MinSublogic OWL_SL SymbMapItems where
    minSublogic _ = sl_top

instance MinSublogic OWL_SL Entity where
    minSublogic _ = sl_top

instance MinSublogic OWL_SL OntologyFile where
    minSublogic = sl_o_file

instance ProjectSublogicM OWL_SL SymbItems where
    projectSublogicM _ i = Just i

instance ProjectSublogicM OWL_SL SymbMapItems where
    projectSublogicM _ i = Just i

instance ProjectSublogicM OWL_SL Entity where
    projectSublogicM _ i = Just i

instance ProjectSublogic OWL_SL OntologyFile where
    projectSublogic = pr_o_file
