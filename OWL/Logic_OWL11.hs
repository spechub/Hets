{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Description :  instance of the class Logic for OWL
Copyright   :  (c) Klaus Lüttich, Heng Jiang, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Here is the place where the class Logic is instantiated for OWL DL.
__SROIQ__
-}

module OWL.Logic_OWL11 where

import Common.AS_Annotation
import Common.DefaultMorphism
import Common.Doc
import Common.DocUtils

import Logic.Logic

import OWL.AS
import OWL.Print ()
import OWL.ATC_OWL ()
import OWL.Sign
import OWL.StaticAnalysis
#ifdef UNI_PACKAGE
import OWL.ProvePellet
#endif

data OWL11 = OWL11 deriving Show

instance Language OWL11 where
 description _ =
  "OWL DL -- Web Ontology Language Description Logic http://wwww.w3c.org/"

type OWL11_Morphism = DefaultMorphism Sign

instance Syntax OWL11 OntologyFile () ()
    -- default implementation is fine!

-- OWL DL logic

instance Sentences OWL11 Sentence Sign OWL11_Morphism () where
    map_sen OWL11 _ s = return s
    print_named OWL11 namedSen =
        pretty (sentence namedSen) <>
           if null (senAttr namedSen) then empty
        else space <> text "%%" <+> text (senAttr namedSen)

instance StaticAnalysis OWL11 OntologyFile Sentence
               () ()
               Sign
               OWL11_Morphism
               () ()   where
{- these functions are be implemented in OWL.StaticAna and OWL.Sign: -}
      basic_analysis OWL11 = Just basicOWL11Analysis
      empty_signature OWL11 = emptySign
      signature_union OWL11 s = return . addSign s
      final_union OWL11 = signature_union OWL11
      inclusion OWL11 = defaultInclusion isSubSign

{-   this function will be implemented in OWL.Taxonomy
         theory_to_taxonomy OWL = convTaxo
-}

instance Logic OWL11 () OntologyFile Sentence () ()
               Sign
               OWL11_Morphism () () ATP_ProofTree where
    --     stability _ = Testing
    -- default implementations are fine
    -- the prover uses HTk and IO functions from uni
#ifdef UNI_PACKAGE
         provers OWL11 = [pelletProver]
         cons_checkers OWL11 = [pelletConsChecker]
#endif
