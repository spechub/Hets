{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Signatures and sentences for OWL 1.1.
Cloned and modified from Sign of OWL DL.
-}

module OWL.Sign where

import OWL.AS
import qualified Data.Set as Set
import qualified Data.Map as Map

type ID = URIreference          -- for universal ID
type OntologyID = URIreference
type ClassID = URIreference
type DatatypeID = URIreference
type IndividualID = URIreference
type DataRoleURI = URIreference
type IndividualRoleURI = URIreference
type AnnotationPropertyID = URIreference

data Sign = Sign
            { ontologyID :: OntologyID -- ^ URL of the ontology
            , concepts :: Set.Set ClassID
              -- ^ a set of classes
            , primaryConcepts :: Set.Set ClassID
              -- ^ a subset of concepts which are not marked
              -- ^ with CASL_Sort = false
            , datatypes :: Set.Set DatatypeID -- ^ a set of datatypes
            , indValuedRoles :: Set.Set IndividualRoleURI
              -- ^ a set of object property
            , dataValuedRoles :: Set.Set DataRoleURI
              -- ^ a set of data property
            , annotationRoles :: Set.Set AnnotationPropertyID
            , individuals :: Set.Set IndividualID  -- ^ a set of individual
              -- ^ a set of axioms of subconceptrelations, domain an drenge
              -- ^of roles, functional roles and concept membership
            , axioms :: Set.Set SignAxiom
            , namespaceMap :: Namespace
            } deriving (Show,Eq,Ord)

data SignAxiom = Subconcept Description Description   -- subclass, superclass
               | RoleDomain ObjectPropertyExpression RDomain
               | RoleRange  ObjectPropertyExpression RRange
               | DataDomain DataPropertyExpression RDomain
               | DataRange DataPropertyExpression RRange
               | FuncRole (RoleType, ObjectPropertyExpression)
               | FuncDataProp DataPropertyExpression
               | RefRole (RoleType, ObjectPropertyExpression)
               | Conceptmembership IndividualID Description
                 deriving (Show,Eq,Ord)

data RoleType = IRole | DRole deriving (Show, Eq, Ord)

data RDomain = RDomain Description
             | DDomain Description
                 deriving (Show,Eq,Ord)

data RRange = RIRange Description
            | RDRange DataRange
              deriving (Show,Eq,Ord)

-- data RoleID = IVP IndividualvaluedPropertyID
--             | DVP DatavaluedPropertyID
--               deriving (Show,Eq,Ord)

data Sentence = OWLAxiom Axiom
              | OWLFact Axiom
                deriving (Show,Eq,Ord)

emptySign :: Sign
emptySign =  Sign { ontologyID = nullQName,
                    concepts = Set.empty,
                    primaryConcepts = Set.empty,
                    datatypes = Set.empty,
                    indValuedRoles = Set.empty,
                    dataValuedRoles = Set.empty,
                    annotationRoles = Set.empty,
                    individuals = Set.empty,
                    axioms = Set.empty,
                    namespaceMap = Map.empty
                  }

simpleSign :: ID -> Sign
simpleSign ontoID =
            emptySign { ontologyID = ontoID }

-- ignoe ontologyID
diffSig :: Sign -> Sign -> Sign
diffSig a b =
    a { concepts = concepts a `Set.difference` concepts b
      , primaryConcepts = primaryConcepts a `Set.difference` primaryConcepts b
      , datatypes = datatypes a `Set.difference` datatypes b
      , indValuedRoles = indValuedRoles a `Set.difference` indValuedRoles b
      , dataValuedRoles = dataValuedRoles a `Set.difference` dataValuedRoles b
      , annotationRoles = annotationRoles a `Set.difference` annotationRoles b
      , individuals = individuals a `Set.difference` individuals b
      , axioms = axioms a `Set.difference` axioms b
      }

addSign :: Sign -> Sign -> Sign
addSign toIns totalSign =
    totalSign { ontologyID = let
                    lp1 = localPart $ ontologyID totalSign
                    lp2 = localPart $ ontologyID toIns
                    in  mkQName $ lp1 ++ "_" ++ lp2,
                concepts = Set.union (concepts totalSign)
                                     (concepts toIns),
                primaryConcepts = Set.union (primaryConcepts totalSign)
                                            (primaryConcepts toIns),
                datatypes = Set.union (datatypes totalSign)
                                      (datatypes toIns),
                indValuedRoles = Set.union (indValuedRoles totalSign)
                                           (indValuedRoles toIns),
                dataValuedRoles = Set.union (dataValuedRoles totalSign)
                                            (dataValuedRoles toIns),
                annotationRoles = Set.union (annotationRoles totalSign)
                                            (annotationRoles toIns),
                individuals = Set.union (individuals totalSign)
                                        (individuals toIns),
                axioms = Set.union (axioms totalSign)
                                   (axioms toIns)
              }

isSubSign :: Sign -> Sign -> Bool
isSubSign a b =
    Set.isSubsetOf (concepts a) (concepts b)
       && Set.isSubsetOf (primaryConcepts a) (primaryConcepts b)
       && Set.isSubsetOf (datatypes a) (datatypes b)
       && Set.isSubsetOf (indValuedRoles a) (indValuedRoles b)
       && Set.isSubsetOf (dataValuedRoles a) (dataValuedRoles b)
       && Set.isSubsetOf (annotationRoles a) (annotationRoles b)
       && Set.isSubsetOf (individuals a) (individuals b)
       && Set.isSubsetOf (axioms a) (axioms b)
