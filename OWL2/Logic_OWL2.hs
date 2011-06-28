{-# LANGUAGE CPP, MultiParamTypeClasses, TypeSynonymInstances #-}
{-# OPTIONS -w #-}
{- |
Module      :  $Header$
Description :  instance of the class Logic for OWL2
Copyright   :  (c) Christian Maeder, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable

Here is the place where the class Logic is instantiated for OWL2.
-}

module OWL2.Logic_OWL2 where

import Common.AS_Annotation
import Common.Doc
import Common.DocUtils
import Common.ProofTree
import Common.DefaultMorphism
import Common.Consistency
import Common.ProverTools

import ATC.ProofTree ()

import Logic.Logic

import OWL2.AS
import OWL2.FS
import OWL2.MS
import OWL2.Parse
import OWL2.ManchesterParser
import OWL2.ManchesterPrint
import OWL2.Symbols
import OWL2.Print ()
import OWL2.FunctionalPrint
import OWL2.ATC_OWL2 ()
import OWL2.Sign
import OWL2.StaticAnalysis
import OWL2.Morphism
--import OWL2.ProvePellet
import OWL2.ProveFact
import OWL2.Conservativity
import OWL2.ColimSign
import OWL2.Taxonomy



type OWLSub = ()

data OWL2 = OWL2 deriving Show

instance Language OWL2 where
 description _ =
  "OWL2 DL -- Web Ontology Language Description Logic http://wwww.w3c.org/"

instance Category Sign OWLMorphism where
    ide sig = inclOWLMorphism sig sig
    dom = osource
    cod = otarget
    legal_mor = legalMor
    isInclusion = isOWLInclusion
    composeMorphisms = composeMor

instance Syntax OWL2 OntologyDocument SymbItems SymbMapItems where
    parse_basic_spec OWL2 = Just basicSpec
    parse_symb_items OWL2 = Just symbItems
    parse_symb_map_items OWL2 = Just symbMapItems

instance Sentences OWL2 Axiom Sign OWLMorphism Entity where
    map_sen OWL2 = mapSen
    print_named OWL2 namedSen =
        pretty $ (if isAxiom namedSen then remImplied else addImplied) (sentence namedSen)
    sym_of OWL2 = singletonList . symOf
    symmap_of OWL2 = symMapOf

instance StaticAnalysis OWL2 OntologyDocument Axiom
               SymbItems SymbMapItems
               Sign
               OWLMorphism
               Entity RawSymb where
      basic_analysis OWL2 = Just basicOWL2Analysis
      stat_symb_items OWL2 _ = return . statSymbItems
      stat_symb_map_items OWL2 _ _ = statSymbMapItems
      empty_signature OWL2 = emptySign
      signature_union OWL2 = uniteSign 
      final_union OWL2 = signature_union OWL2
      is_subsig OWL2 = isSubSign
      subsig_inclusion OWL2 s = return . inclOWLMorphism s
      matches OWL2 = matchesSym
      symbol_to_raw OWL2 = ASymbol
      induced_from_morphism OWL2 = inducedFromMor
      cogenerated_sign OWL2 = cogeneratedSign
      generated_sign OWL2 = generatedSign
      signature_colimit OWL2 = return . signColimit
#ifdef UNI_PACKAGE
      theory_to_taxonomy OWL2 = onto2Tax
#endif
instance Logic OWL2 OWLSub OntologyDocument Axiom SymbItems SymbMapItems
               Sign
               OWLMorphism Entity RawSymb ProofTree where
         empty_proof_tree OWL2 = emptyProofTree
#ifdef UNI_PACKAGE
         provers OWL2 = unsafeFileCheck "OWLFactProver.jar" hetsOWLenv factProver
         cons_checkers OWL2 = unsafeFileCheck "OWLFact.jar" hetsOWLenv factConsChecker
         conservativityCheck OWL2 = concatMap
           (\ ct -> unsafeFileCheck localityJar hetsOWLenv
              $ ConservativityChecker ("Locality_" ++ ct)
                      $ conserCheck ct)
           ["BOTTOM_BOTTOM", "TOP_BOTTOM", "TOP_TOP"]
	
#endif
{-
instance SemiLatticeWithTop OWLSub where
    join = sl_max
    top = sl_top

instance SublogicName OWLSub where
    sublogicName = sl_name

instance MinSublogic OWLSub Axiom where
    minSublogic = sl_ax

instance MinSublogic OWLSub OWLMorphism where
    minSublogic = sl_mor

instance ProjectSublogic OWLSub OWLMorphism where
    projectSublogic = pr_mor

instance MinSublogic OWLSub Sign where
    minSublogic = sl_sig

instance ProjectSublogic OWLSub Sign where
    projectSublogic = pr_sig

instance MinSublogic OWLSub SymbItems where
    minSublogic = const sl_top

instance MinSublogic OWLSub SymbMapItems where
    minSublogic = const sl_top

instance MinSublogic OWLSub Entity where
    minSublogic = const sl_top

instance MinSublogic OWLSub OntologyFile where
    minSublogic = sl_o_file

instance ProjectSublogicM OWLSub SymbItems where
    projectSublogicM = const Just

instance ProjectSublogicM OWLSub SymbMapItems where
    projectSublogicM = const Just

instance ProjectSublogicM OWLSub Entity where
    projectSublogicM = const Just

instance ProjectSublogic OWLSub OntologyFile where
    projectSublogic = pr_o_file
-}
