{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Heng Jiang, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  portable

Here is the place where the class Logic is instantiated for OWL DL.
   Also the instances for Syntax an Category.
-}

{- todo:
    - fill instance StaticAna with life

-}

module OWL_DL.Logic_OWL_DL where

import Data.Dynamic

import Common.DynamicUtils
-- import Common.Result
import Common.AS_Annotation
import Common.DefaultMorphism
import Common.Lib.Pretty
import Common.PrettyPrint

import Logic.Logic

import OWL_DL.AS
import OWL_DL.Print
import OWL_DL.ATC_OWL_DL
import OWL_DL.Sign
-- import Logic.Comorphism
import OWL_DL.StaticAna


data OWL_DL = OWL_DL deriving Show

instance Language OWL_DL where
 description _ = 
  "OWL DL -- Web Ontology Language Description Logic http://wwww.w3c.org/"


-- Typeable instance
tc_Sign, tc_Sentence, tc_Ontology :: TyCon

tc_Sign = mkTyCon "OWL_DL.Sign.Sign"
tc_Sentence = mkTyCon "OWL_DL.Sign.Sentence"
tc_Ontology     = mkTyCon "OWL_DL.AS.Ontology"

instance Typeable Sign where
  typeOf _ = mkTyConApp tc_Sign []
instance Typeable Sentence where
  typeOf _ = mkTyConApp tc_Sentence []
instance Typeable Ontology where
      typeOf _ = mkTyConApp tc_Ontology []
type OWL_DLMorphism = DefaultMorphism Sign

instance Category OWL_DL Sign OWL_DLMorphism  
    where
  dom OWL_DL = domOfDefaultMorphism
  cod OWL_DL = codOfDefaultMorphism
  ide OWL_DL = ideOfDefaultMorphism
  comp OWL_DL = compOfDefaultMorphism
  legal_obj OWL_DL = const True
  legal_mor OWL_DL = legalDefaultMorphism (legal_obj OWL_DL)

-- abstract syntax, parsing (and printing)

instance Syntax OWL_DL Ontology () ()
    -- default implementation is fine!


-- OWL DL logic

instance Sentences OWL_DL Sentence () Sign OWL_DLMorphism () where
    map_sen OWL_DL _ s = return s
    print_named OWL_DL ga namedSen = 
        printText0 ga (sentence namedSen) <>
           if null (senName namedSen) then empty 
        else space <> text "%%" <+> text (senName namedSen) 
    provers OWL_DL = [] 
    cons_checkers OWL_DL = []


instance StaticAnalysis OWL_DL Ontology Sentence ()
               () ()
               Sign 
               OWL_DLMorphism 
               () ()   where
{- these functions will be implemented in OWL_DL.StaticAna and OWL_DL.Sign: -} 
      basic_analysis OWL_DL = Just basicOWL_DLAnalysis 
      empty_signature OWL_DL = emptySign
      signature_union OWL_DL s = return . addSign s
      final_union OWL_DL = signature_union OWL_DL
      inclusion OWL_DL = defaultInclusion (is_subsig OWL_DL)
      is_subsig OWL_DL = isSubSign


{-   this function will be implemented in OWL_DL.Taxonomy
         theory_to_taxonomy OWL_DL = convTaxo
-}

instance Logic OWL_DL ()
               Ontology Sentence () ()
               Sign 
               OWL_DLMorphism
               () () () 

{-
instance Comorphism OWL_DL
               OWL_DL ()
               () Sentence () ()
               Sign OWL_DLMorphism
               () () ()
               OWL_DL ()
               () Sentence () ()
               Sign OWL_DLMorphism
               () () ()
-}
