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

import Data.Char (isAlpha)
import qualified Data.Set as Set

import ATC.ProofTree ()

import Logic.Logic

import OWL2.AS
import OWL2.MS
import OWL2.MS2Ship
import OWL2.Theorem
import OWL2.Parse
import OWL2.ManchesterParser
import OWL2.ManchesterPrint
import OWL2.Symbols
import OWL2.Print ()
import OWL2.ATC_OWL2 ()
import OWL2.Sign
import OWL2.StaticAnalysis
import OWL2.Morphism
import OWL2.ProvePellet
import OWL2.ProveFact
import OWL2.Conservativity
import OWL2.ColimSign
import OWL2.Taxonomy
import OWL2.ProfilesAndSublogics
import OWL2.Rename

data OWL2 = OWL2 deriving Show

instance Language OWL2 where
  language_name _ = "OWL"
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
    parsersAndPrinters OWL2 = addSyntax "Ship" (basicSpec, ppShipOnt)
      $ makeDefault (basicSpec, pretty)
    parse_symb_items OWL2 = Just symbItems
    parse_symb_map_items OWL2 = Just symbMapItems

instance Sentences OWL2 Axiom Sign OWLMorphism Entity where
    map_sen OWL2 = mapSen
    print_named OWL2 = printOneNamed
    printTheory OWL2 = printBasicTheory
    sym_of OWL2 = singletonList . symOf
    symmap_of OWL2 = symMapOf
    sym_name OWL2 = entityToId
    symKind OWL2 = takeWhile isAlpha . showEntityType . entityKind
    symsOfSen OWL2 = Set.toList . symsOfAxiom

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
      signatureDiff OWL2 s = return . diffSig s
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
instance Logic OWL2 ProfSub OntologyDocument Axiom SymbItems SymbMapItems
               Sign
               OWLMorphism Entity RawSymb ProofTree where
         empty_proof_tree OWL2 = emptyProofTree
         -- just a selection of sublogics
         all_sublogics OWL2 = bottomS : concat allProfSubs ++ [topS]
         bottomSublogic OWL2 = Just bottomS
         sublogicDimensions OWL2 = allProfSubs
         parseSublogic OWL2 _ = Just topS -- ignore sublogics
#ifdef UNI_PACKAGE
         provers OWL2 = unsafeFileCheck pelletJar pelletEnv pelletProver ++
            unsafeFileCheck pelletJar pelletEnv pelletEL ++
             (unsafeFileCheck "OWLFactProver.jar" hetsOWLenv factProver)
         cons_checkers OWL2 =
             (unsafeFileCheck pelletJar pelletEnv pelletConsChecker) ++
             (unsafeFileCheck "OWLFact.jar" hetsOWLenv factConsChecker)
         conservativityCheck OWL2 = concatMap
           (\ ct -> unsafeFileCheck localityJar hetsOWLenv
              $ ConservativityChecker ("Locality_" ++ ct)
                      $ conserCheck ct)
           ["BOTTOM_BOTTOM", "TOP_BOTTOM", "TOP_TOP"]

#endif

instance SemiLatticeWithTop ProfSub where
    join = maxS
    top = topS

instance SublogicName ProfSub where
    sublogicName = nameS

instance MinSublogic ProfSub Axiom where
    minSublogic = psAxiom

instance MinSublogic ProfSub OWLMorphism where
    minSublogic = sMorph

instance ProjectSublogic ProfSub OWLMorphism where
    projectSublogic = prMorph

instance MinSublogic ProfSub Sign where
    minSublogic = sSig

instance ProjectSublogic ProfSub Sign where
    projectSublogic = prSign

instance MinSublogic ProfSub SymbItems where
    minSublogic = const topS

instance MinSublogic ProfSub SymbMapItems where
    minSublogic = const topS

instance MinSublogic ProfSub Entity where
    minSublogic = const topS

instance MinSublogic ProfSub OntologyDocument where
    minSublogic = profilesAndSublogic

instance ProjectSublogicM ProfSub SymbItems where
    projectSublogicM = const Just

instance ProjectSublogicM ProfSub SymbMapItems where
    projectSublogicM = const Just

instance ProjectSublogicM ProfSub Entity where
    projectSublogicM = const Just

instance ProjectSublogic ProfSub OntologyDocument where
    projectSublogic = prOntDoc
