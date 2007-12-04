{- |
Module      :  $Header$
Description :  instance of the class Logic for OWL_DL
Copyright   :  (c) Klaus Lüttich, Heng Jiang, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Here is the place where the class Logic is instantiated for OWL DL.
__SROIQ__
-}

module OWL_DL.OWL11.Logic_OWL11 where

import Common.AS_Annotation
import Common.DefaultMorphism
import Common.Doc
import Common.DocUtils

import Logic.Logic

import OWL_DL.OWL11.FFS
import OWL_DL.OWL11.Print ()
import OWL_DL.OWL11.ATC_OWL11 ()
import OWL_DL.OWL11.Sign
import OWL_DL.OWL11.StaticAnalysis

data OWL11 = OWL11 deriving Show

instance Language OWL11 where
 description _ =
  "OWL DL -- Web Ontology Language Description Logic http://wwww.w3c.org/"

type OWL11_Morphism = DefaultMorphism Sign

instance Category OWL11 Sign OWL11_Morphism
    where
  dom OWL11 = domOfDefaultMorphism
  cod OWL11 = codOfDefaultMorphism
  ide OWL11 = ideOfDefaultMorphism
  comp OWL11 = compOfDefaultMorphism
  legal_obj OWL11 = const True
  legal_mor OWL11 = legalDefaultMorphism (legal_obj OWL11)

-- abstract syntax, parsing (and printing)

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
{- these functions are be implemented in OWL_DL.StaticAna and OWL_DL.Sign: -}
      basic_analysis OWL11 = Just basicOWL11Analysis
      empty_signature OWL11 = emptySign
      signature_union OWL11 s = return . addSign s
      final_union OWL11 = signature_union OWL11
      inclusion OWL11 = defaultInclusion (is_subsig OWL11)
      is_subsig OWL11 = isSubSign


{-   this function will be implemented in OWL_DL.Taxonomy
         theory_to_taxonomy OWL_DL = convTaxo
-}

instance Logic OWL11 ()
               OntologyFile Sentence () ()
               Sign
               OWL11_Morphism
               () () () where
      empty_proof_tree _ = ()

