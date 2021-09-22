{- |
Module      :  ./OWL2/Theorem.hs
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Adds the "implied" annotation - for specifying theorems
-}

module OWL2.Theorem where

import Common.IRI
import qualified OWL2.AS as AS
import OWL2.MS

import Data.List

implied :: AS.Annotation
implied = AS.Annotation [] (mkIRI "Implied")
  . AS.AnnValLit . AS.Literal "true" . AS.Typed $ mkIRI "string"

rmList :: Annotations -> Annotations
rmList = filter (not . prove1)

rmImplied :: AS.Axiom -> AS.Axiom
rmImplied ax = case ax of
    AS.Declaration anns a -> AS.Declaration (rmList anns) a 
    AS.ClassAxiom cax -> case cax of
        AS.SubClassOf anns a b -> AS.ClassAxiom $ AS.SubClassOf (rmList anns)  a b 
        AS.EquivalentClasses anns a -> AS.ClassAxiom $ AS.EquivalentClasses (rmList anns)  a 
        AS.DisjointClasses anns a -> AS.ClassAxiom $ AS.DisjointClasses (rmList anns)  a 
        AS.DisjointUnion anns a b -> AS.ClassAxiom $ AS.DisjointUnion (rmList anns) a b 
    AS.ObjectPropertyAxiom opax -> case opax of
        AS.SubObjectPropertyOf anns a b -> AS.ObjectPropertyAxiom $ AS.SubObjectPropertyOf (rmList anns)  a b 
        AS.EquivalentObjectProperties anns a -> AS.ObjectPropertyAxiom $ AS.EquivalentObjectProperties (rmList anns)  a 
        AS.DisjointObjectProperties anns a -> AS.ObjectPropertyAxiom $ AS.DisjointObjectProperties (rmList anns) a 
        AS.InverseObjectProperties anns a b -> AS.ObjectPropertyAxiom $ AS.InverseObjectProperties (rmList anns) a b 
        AS.ObjectPropertyDomain anns a b -> AS.ObjectPropertyAxiom $ AS.ObjectPropertyDomain (rmList anns)  a b 
        AS.ObjectPropertyRange anns a b -> AS.ObjectPropertyAxiom $ AS.ObjectPropertyRange (rmList anns)  a b 
        AS.FunctionalObjectProperty anns a -> AS.ObjectPropertyAxiom $ AS.FunctionalObjectProperty (rmList anns)  a 
        AS.InverseFunctionalObjectProperty anns a -> AS.ObjectPropertyAxiom $ AS.InverseFunctionalObjectProperty (rmList anns)  a 
        AS.ReflexiveObjectProperty anns a -> AS.ObjectPropertyAxiom $ AS.ReflexiveObjectProperty (rmList anns)  a 
        AS.IrreflexiveObjectProperty anns a -> AS.ObjectPropertyAxiom $ AS.IrreflexiveObjectProperty (rmList anns)  a 
        AS.SymmetricObjectProperty anns a -> AS.ObjectPropertyAxiom $ AS.SymmetricObjectProperty (rmList anns)  a 
        AS.AsymmetricObjectProperty anns a -> AS.ObjectPropertyAxiom $ AS.AsymmetricObjectProperty (rmList anns)  a 
        AS.TransitiveObjectProperty anns a -> AS.ObjectPropertyAxiom $ AS.TransitiveObjectProperty (rmList anns)  a 
    AS.DataPropertyAxiom dpax -> case dpax of
        AS.SubDataPropertyOf anns a b -> AS.DataPropertyAxiom $ AS.SubDataPropertyOf (rmList anns)  a b 
        AS.EquivalentDataProperties anns a -> AS.DataPropertyAxiom $ AS.EquivalentDataProperties (rmList anns)  a 
        AS.DisjointDataProperties anns a -> AS.DataPropertyAxiom $ AS.DisjointDataProperties (rmList anns)  a 
        AS.DataPropertyDomain anns a b -> AS.DataPropertyAxiom $ AS.DataPropertyDomain (rmList anns)  a b 
        AS.DataPropertyRange anns a b -> AS.DataPropertyAxiom $ AS.DataPropertyRange (rmList anns)  a b 
        AS.FunctionalDataProperty anns a -> AS.DataPropertyAxiom $ AS.FunctionalDataProperty (rmList anns)  a 
    AS.DatatypeDefinition anns a b -> AS.DatatypeDefinition (rmList anns)  a b 
    AS.HasKey anns a b c -> AS.HasKey (rmList anns)  a b c 
    AS.Assertion assertion -> case assertion of
        AS.SameIndividual anns a -> AS.Assertion $ AS.SameIndividual (rmList anns)  a 
        AS.DifferentIndividuals anns a -> AS.Assertion $ AS.DifferentIndividuals (rmList anns)  a 
        AS.ClassAssertion anns a b -> AS.Assertion $ AS.ClassAssertion (rmList anns)  a b 
        AS.ObjectPropertyAssertion anns a b c -> AS.Assertion $ AS.ObjectPropertyAssertion (rmList anns)  a b c 
        AS.NegativeObjectPropertyAssertion anns a b c -> AS.Assertion $ AS.NegativeObjectPropertyAssertion (rmList anns)  a b c 
        AS.DataPropertyAssertion anns a b c -> AS.Assertion $ AS.DataPropertyAssertion (rmList anns)  a b c 
        AS.NegativeDataPropertyAssertion anns a b c -> AS.Assertion $ AS.NegativeDataPropertyAssertion (rmList anns) a b c 
    AS.AnnotationAxiom annax -> case annax of
        AS.AnnotationAssertion anns a b c -> AS.AnnotationAxiom $ AS.AnnotationAssertion (rmList anns)  a b c 
        AS.SubAnnotationPropertyOf anns a b -> AS.AnnotationAxiom $ AS.SubAnnotationPropertyOf (rmList anns)  a b 
        AS.AnnotationPropertyDomain anns a b -> AS.AnnotationAxiom $ AS.AnnotationPropertyDomain (rmList anns)  a b 
        AS.AnnotationPropertyRange anns a b -> AS.AnnotationAxiom $ AS.AnnotationPropertyRange (rmList anns)  a b 
    AS.DGAxiom anns a b c d -> AS.DGAxiom (rmList anns) a b c d 

addImplied :: AS.Axiom -> AS.Axiom
addImplied ax = case ax of
    AS.Declaration anns a -> AS.Declaration (implied : anns) a 
    AS.ClassAxiom cax -> case cax of
        AS.SubClassOf anns a b -> AS.ClassAxiom $ AS.SubClassOf (implied : anns)  a b 
        AS.EquivalentClasses anns a -> AS.ClassAxiom $ AS.EquivalentClasses (implied : anns)  a 
        AS.DisjointClasses anns a -> AS.ClassAxiom $ AS.DisjointClasses (implied : anns)  a 
        AS.DisjointUnion anns a b -> AS.ClassAxiom $ AS.DisjointUnion (implied : anns) a b 
    AS.ObjectPropertyAxiom opax -> case opax of
        AS.SubObjectPropertyOf anns a b -> AS.ObjectPropertyAxiom $ AS.SubObjectPropertyOf (implied : anns)  a b 
        AS.EquivalentObjectProperties anns a -> AS.ObjectPropertyAxiom $ AS.EquivalentObjectProperties (implied : anns)  a 
        AS.DisjointObjectProperties anns a -> AS.ObjectPropertyAxiom $ AS.DisjointObjectProperties (implied : anns) a 
        AS.InverseObjectProperties anns a b -> AS.ObjectPropertyAxiom $ AS.InverseObjectProperties (implied : anns) a b 
        AS.ObjectPropertyDomain anns a b -> AS.ObjectPropertyAxiom $ AS.ObjectPropertyDomain (implied : anns)  a b 
        AS.ObjectPropertyRange anns a b -> AS.ObjectPropertyAxiom $ AS.ObjectPropertyRange (implied : anns)  a b 
        AS.FunctionalObjectProperty anns a -> AS.ObjectPropertyAxiom $ AS.FunctionalObjectProperty (implied : anns)  a 
        AS.InverseFunctionalObjectProperty anns a -> AS.ObjectPropertyAxiom $ AS.InverseFunctionalObjectProperty (implied : anns)  a 
        AS.ReflexiveObjectProperty anns a -> AS.ObjectPropertyAxiom $ AS.ReflexiveObjectProperty (implied : anns)  a 
        AS.IrreflexiveObjectProperty anns a -> AS.ObjectPropertyAxiom $ AS.IrreflexiveObjectProperty (implied : anns)  a 
        AS.SymmetricObjectProperty anns a -> AS.ObjectPropertyAxiom $ AS.SymmetricObjectProperty (implied : anns)  a 
        AS.AsymmetricObjectProperty anns a -> AS.ObjectPropertyAxiom $ AS.AsymmetricObjectProperty (implied : anns)  a 
        AS.TransitiveObjectProperty anns a -> AS.ObjectPropertyAxiom $ AS.TransitiveObjectProperty (implied : anns)  a 
    AS.DataPropertyAxiom dpax -> case dpax of
        AS.SubDataPropertyOf anns a b -> AS.DataPropertyAxiom $ AS.SubDataPropertyOf (implied : anns)  a b 
        AS.EquivalentDataProperties anns a -> AS.DataPropertyAxiom $ AS.EquivalentDataProperties (implied : anns)  a 
        AS.DisjointDataProperties anns a -> AS.DataPropertyAxiom $ AS.DisjointDataProperties (implied : anns)  a 
        AS.DataPropertyDomain anns a b -> AS.DataPropertyAxiom $ AS.DataPropertyDomain (implied : anns)  a b 
        AS.DataPropertyRange anns a b -> AS.DataPropertyAxiom $ AS.DataPropertyRange (implied : anns)  a b 
        AS.FunctionalDataProperty anns a -> AS.DataPropertyAxiom $ AS.FunctionalDataProperty (implied : anns)  a 
    AS.DatatypeDefinition anns a b -> AS.DatatypeDefinition (implied : anns)  a b 
    AS.HasKey anns a b c -> AS.HasKey (implied : anns)  a b c 
    AS.Assertion assertion -> case assertion of
        AS.SameIndividual anns a -> AS.Assertion $ AS.SameIndividual (implied : anns)  a 
        AS.DifferentIndividuals anns a -> AS.Assertion $ AS.DifferentIndividuals (implied : anns)  a 
        AS.ClassAssertion anns a b -> AS.Assertion $ AS.ClassAssertion (implied : anns)  a b 
        AS.ObjectPropertyAssertion anns a b c -> AS.Assertion $ AS.ObjectPropertyAssertion (implied : anns)  a b c 
        AS.NegativeObjectPropertyAssertion anns a b c -> AS.Assertion $ AS.NegativeObjectPropertyAssertion (implied : anns)  a b c 
        AS.DataPropertyAssertion anns a b c -> AS.Assertion $ AS.DataPropertyAssertion (implied : anns)  a b c 
        AS.NegativeDataPropertyAssertion anns a b c -> AS.Assertion $ AS.NegativeDataPropertyAssertion (implied : anns) a b c 
    AS.AnnotationAxiom anax -> case anax of
        AS.AnnotationAssertion anns a b c -> AS.AnnotationAxiom $ AS.AnnotationAssertion (implied : anns)  a b c 
        AS.SubAnnotationPropertyOf anns a b -> AS.AnnotationAxiom $ AS.SubAnnotationPropertyOf (implied : anns)  a b 
        AS.AnnotationPropertyDomain anns a b -> AS.AnnotationAxiom $ AS.AnnotationPropertyDomain (implied : anns)  a b 
        AS.AnnotationPropertyRange anns a b -> AS.AnnotationAxiom $ AS.AnnotationPropertyRange (implied : anns)  a b 
    AS.DGAxiom anns a b c d -> AS.DGAxiom (implied : anns) a b c d 

prove1 :: AS.Annotation -> Bool
prove1 anno = case anno of
      AS.Annotation _ aIRI (AS.AnnValLit (AS.Literal value (AS.Typed _))) ->
          show (iriPath aIRI) == "Implied" && isInfixOf "true" value
      _ -> False

proveAnnos :: [AS.Annotation] -> Bool
proveAnnos = any prove1

prove :: AS.Axiom -> Bool
prove ax = case ax of
    AS.Declaration anns _ -> proveAnnos anns
    AS.ClassAxiom cax -> case cax of
        AS.SubClassOf anns _ _ -> proveAnnos anns
        AS.EquivalentClasses anns _ -> proveAnnos anns
        AS.DisjointClasses anns _ -> proveAnnos anns
        AS.DisjointUnion anns _ _ -> proveAnnos anns
    AS.ObjectPropertyAxiom opax -> case opax of
        AS.SubObjectPropertyOf anns _ _ -> proveAnnos anns
        AS.EquivalentObjectProperties anns _ -> proveAnnos anns
        AS.DisjointObjectProperties anns _ -> proveAnnos anns
        AS.InverseObjectProperties anns _ _ -> proveAnnos anns
        AS.ObjectPropertyDomain anns _ _ -> proveAnnos anns
        AS.ObjectPropertyRange anns _ _ -> proveAnnos anns
        AS.FunctionalObjectProperty anns _ -> proveAnnos anns
        AS.InverseFunctionalObjectProperty anns _ -> proveAnnos anns
        AS.ReflexiveObjectProperty anns _ -> proveAnnos anns
        AS.IrreflexiveObjectProperty anns _ -> proveAnnos anns
        AS.SymmetricObjectProperty anns _ -> proveAnnos anns
        AS.AsymmetricObjectProperty anns _ -> proveAnnos anns
        AS.TransitiveObjectProperty anns _ -> proveAnnos anns
    AS.DataPropertyAxiom a -> case a of
        AS.SubDataPropertyOf anns _ _ -> proveAnnos anns
        AS.EquivalentDataProperties anns _ -> proveAnnos anns
        AS.DisjointDataProperties anns _ -> proveAnnos anns
        AS.DataPropertyDomain anns _ _ -> proveAnnos anns
        AS.DataPropertyRange anns _ _ -> proveAnnos anns
        AS.FunctionalDataProperty anns _ -> proveAnnos anns
    AS.DatatypeDefinition anns _ _ -> proveAnnos anns
    AS.HasKey anns _ _ _ -> proveAnnos anns
    AS.Assertion a -> case a of
        AS.SameIndividual anns _ -> proveAnnos anns
        AS.DifferentIndividuals anns _ -> proveAnnos anns
        AS.ClassAssertion anns _ _ -> proveAnnos anns
        AS.ObjectPropertyAssertion anns _ _ _ -> proveAnnos anns
        AS.NegativeObjectPropertyAssertion anns _ _ _ -> proveAnnos anns
        AS.DataPropertyAssertion anns _ _ _ -> proveAnnos anns
        AS.NegativeDataPropertyAssertion anns _ _ _ -> proveAnnos anns
    AS.AnnotationAxiom a -> case a of
        AS.AnnotationAssertion anns _ _ _ -> proveAnnos anns
        AS.SubAnnotationPropertyOf anns _ _ -> proveAnnos anns
        AS.AnnotationPropertyDomain anns _ _ -> proveAnnos anns
        AS.AnnotationPropertyRange anns _ _ -> proveAnnos anns
    AS.DGAxiom anns _ _ _ _ -> proveAnnos anns
