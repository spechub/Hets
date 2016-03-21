{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, University of Madgeburg, 2016
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till@iws.cs.ovgu.de
Stability   :  provisional
Portability :  portable

Pretty printing for OWL 2
-}

module OWL2.GenericPrint where

import qualified OWL2.ManchesterPrint as MPrint
import qualified OWL2.FunctionalPrint as FPrint
import qualified OWL2.MS2Ship as Ship

import Common.Doc
import Common.DocUtils
import OWL2.MS

import qualified Data.Set as Set
import OWL2.Sign
import Common.AS_Annotation as Anno

instance PrettyWithString OntologyDocument where
 prettyWithString "Functional" = FPrint.printOntologyDocument
 prettyWithString "Manchester" = MPrint.printOntologyDocument
 prettyWithString "Ship" = Ship.ppShipOnt
 prettyWithString x = error $ "unsupported syntax for OWL:" ++ x

instance Pretty OntologyDocument where
 pretty = prettyWithString "Functional"

instance PrettyWithString Sign where
    prettyWithString "Functional" = FPrint.printSign
    prettyWithString "Manchester" = MPrint.printSign
    prettyWithString x = error $ "unsupported syntax for OWL:" ++ x

instance PrettyWithString Fact where
    prettyWithString "Functional" = FPrint.printFact
    prettyWithString "Manchester" = MPrint.printFact
    prettyWithString x = error $ "unsupported syntax for OWL:" ++ x

instance PrettyWithString ListFrameBit where
    prettyWithString "Functional" = FPrint.printListFrameBit
    prettyWithString "Manchester" = MPrint.printListFrameBit
    prettyWithString x = error $ "unsupported syntax for OWL:" ++ x

instance PrettyWithString Frame where
    prettyWithString "Functional" = FPrint.printFrame
    prettyWithString "Manchester" = MPrint.printFrame
    prettyWithString x = error $ "unsupported syntax for OWL:" ++ x

instance PrettyWithString Axiom where
    prettyWithString "Functional" = FPrint.printAxiom
    prettyWithString "Manchester" = MPrint.printAxiom
    prettyWithString x = error $ "unsupported syntax for OWL:" ++ x

instance Pretty Axiom where 
  pretty = prettyWithString "Functional"

instance Pretty Sign where
  pretty = prettyWithString "Functional"

-- | Printing the ontology
instance PrettyWithString Ontology where
    prettyWithString "Functional" = FPrint.printOntology
    prettyWithString "Manchester" = MPrint.printOntology
    prettyWithString x = error $ "unsupported syntax for OWL:" ++ x

printOneNamed :: String -> Anno.Named Axiom -> Doc
printOneNamed str ns = 
 case str of 
  "Functional" -> FPrint.printOneNamed ns
  "Manchester" -> MPrint.printOneNamed ns
  x -> error $ "unsupported syntax for OWL:" ++ x 

convertBasicTheory :: String -> (Sign, [Named Axiom]) -> OntologyDocument
convertBasicTheory str th = 
  case str of 
  "Functional" -> FPrint.convertBasicTheory th
  "Manchester" -> MPrint.convertBasicTheory th
  x -> error $ "unsupported syntax for OWL:" ++ x 


