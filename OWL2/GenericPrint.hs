{-# LANGUAGE MultiParamTypeClasses #-}
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
import qualified OWL2.ManchesterPrintBasic as MPrintBasic
import qualified OWL2.FunctionalPrintBasic as FPrintBasic
import qualified OWL2.MS2Ship as Ship

import Common.Doc
import Common.DocUtils
import OWL2.MS

import qualified Data.Set as Set
import OWL2.Sign
import OWL2.AS
import Common.AS_Annotation as Anno

data OWLSerializations = FunctionalSyntax | ManchesterSyntax | ShipFormat
  deriving Show

instance MultiPretty OWLSerializations OntologyDocument where
 multiPretty FunctionalSyntax = FPrint.printOntologyDocument
 multiPretty ManchesterSyntax = MPrint.printOntologyDocument
 multiPretty ShipFormat = Ship.ppShipOnt
 multiPretty x = error $ "unsupported syntax for OWL:" ++ show x

instance Pretty OntologyDocument where
 pretty = multiPretty FunctionalSyntax

instance MultiPretty OWLSerializations Sign where
    multiPretty FunctionalSyntax = FPrint.printSign
    multiPretty ManchesterSyntax = MPrint.printSign
    multiPretty x = error $ "unsupported syntax for OWL:" ++ show x

instance MultiPretty OWLSerializations ListFrameBit where
    multiPretty FunctionalSyntax = FPrint.printListFrameBit
    multiPretty ManchesterSyntax = MPrint.printListFrameBit
    multiPretty x = error $ "unsupported syntax for OWL:" ++ show x

instance MultiPretty OWLSerializations Frame where
    multiPretty FunctionalSyntax = FPrint.printFrame
    multiPretty ManchesterSyntax = MPrint.printFrame
    multiPretty x = error $ "unsupported syntax for OWL:" ++ show x

instance MultiPretty OWLSerializations Axiom where
    multiPretty FunctionalSyntax = FPrint.printAxiom
    multiPretty ManchesterSyntax = MPrint.printAxiom
    multiPretty x = error $ "unsupported syntax for OWL:" ++ show x

instance Pretty Axiom where 
  pretty = multiPretty FunctionalSyntax

instance Pretty Sign where
  pretty = multiPretty FunctionalSyntax

-- | Printing the ontology
instance MultiPretty OWLSerializations Ontology where
    multiPretty FunctionalSyntax = FPrint.printOntology
    multiPretty ManchesterSyntax = MPrint.printOntology
    multiPretty x = error $ "unsupported syntax for OWL:" ++ show x

printOneNamed :: OWLSerializations -> Anno.Named Axiom -> Doc
printOneNamed str ns = 
 case str of 
  FunctionalSyntax -> FPrint.printOneNamed ns
  ManchesterSyntax -> MPrint.printOneNamed ns
  x -> error $ "unsupported syntax for OWL:" ++ show x 

convertBasicTheory :: OWLSerializations -> (Sign, [Named Axiom]) -> OntologyDocument
convertBasicTheory str th = 
  case str of 
  FunctionalSyntax -> FPrint.convertBasicTheory th
  ManchesterSyntax -> MPrint.convertBasicTheory th
  x -> error $ "unsupported syntax for OWL:" ++ show x 

instance Pretty QName where
 pretty = FPrintBasic.printIRI

instance Pretty Entity where
 pretty = FPrintBasic.printEntity

instance Pretty ClassExpression where
 pretty = FPrintBasic.printClassExpression

instance Pretty ListFrameBit where
 pretty = FPrint.printListFrameBit

instance Pretty Fact where
 pretty = MPrint.printFact -- for now!


