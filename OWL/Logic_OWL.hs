{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Description :  instance of the class Logic for OWL
Copyright   :  (c) Klaus Luettich, Heng Jiang, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Here is the place where the class Logic is instantiated for OWL DL.
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
#ifdef UNI_PACKAGE
import OWL.ProvePellet
#endif

data OWL = OWL deriving Show

instance Language OWL where
 description _ =
  "OWL DL -- Web Ontology Language Description Logic http://wwww.w3c.org/"

type OWL_Morphism = DefaultMorphism Sign

instance Syntax OWL OntologyFile () () where
    parse_basic_spec OWL = Just basicSpec

-- OWL DL logic

instance Sentences OWL Sentence Sign OWL_Morphism () where
    map_sen OWL _ s = return s
    print_named OWL namedSen =
        pretty (sentence namedSen) <>
          if isAxiom namedSen then empty else space <> text "%implied"

instance StaticAnalysis OWL OntologyFile Sentence
               () ()
               Sign
               OWL_Morphism
               () ()   where
{- these functions are be implemented in OWL.StaticAna and OWL.Sign: -}
      basic_analysis OWL = Just basicOWLAnalysis
      empty_signature OWL = emptySign
      signature_union OWL s = return . addSign s
      final_union OWL = signature_union OWL
      inclusion OWL = defaultInclusion isSubSign

{-   this function will be implemented in OWL.Taxonomy
         theory_to_taxonomy OWL = convTaxo
-}

instance Logic OWL () OntologyFile Sentence () ()
               Sign
               OWL_Morphism () () ProofTree where
    --     stability _ = Testing
    -- default implementations are fine
    -- the prover uses HTk and IO functions from uni
#ifdef UNI_PACKAGE
         provers OWL = [pelletProver]
         cons_checkers OWL = [pelletConsChecker]
#endif
