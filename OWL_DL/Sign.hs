{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@tzi.de
Stability   :  provisional
Portability :  portable

Signatures and sentences for OWL_DL.
-}

module OWL_DL.Sign where

import OWL_DL.AS
import Text.XML.HXT.DOM.XmlTreeTypes
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Map as Map

data Sign = Sign
            { ontologyID :: URIreference -- ^ URL of the ontology
            , concepts :: Set.Set URIreference 
              -- ^ a set of classes
            , primaryConcepts :: Set.Set URIreference 
              -- ^ a subset of concepts which are not marked 
              -- with CASL_Sort = false
            , datatypes :: Set.Set URIreference -- ^ a set of datatypes
            , indValuedRoles :: Set.Set URIreference 
              -- ^ a set of object property
            , dataValuedRoles :: Set.Set URIreference 
              -- ^ a set of data property
            , annotationRoles :: Set.Set URIreference
            , individuals :: Set.Set IndividualID  -- ^ a set of individual
              -- ^ a set of axioms of subconceptrelations, domain an drenge 
              -- ^of roles, functional roles and concept membership
            , axioms :: Set.Set SignAxiom
            , namespaceMap :: Namespace
            } deriving (Show,Eq,Ord)

data SignAxiom = Subconcept ClassID ClassID       -- subclass, superclass
               | RoleDomain ID RDomain
               | RoleRange  ID RRange
               | FuncRole   ID
               | Conceptmembership IndividualID Description
                 deriving (Show,Eq,Ord)

data RDomain = RDomain Description
                 deriving (Show,Eq,Ord)

data RRange = RIRange Description
            | RDRange DataRange
	      deriving (Show,Eq,Ord)

-- data RoleID = IVP IndividualvaluedPropertyID 
--             | DVP DatavaluedPropertyID
--         	 deriving (Show,Eq,Ord)

type ID = URIreference          -- for universal ID

data Sentence = OWLAxiom Axiom                       
              | OWLFact Fact
                deriving (Show,Eq,Ord)

emptySign :: Sign
emptySign =  Sign { ontologyID = QN "" "" "", 
                    concepts = Set.empty,
		    primaryConcepts = Set.empty,
		    datatypes = Set.empty,
		    indValuedRoles = Set.empty,
		    dataValuedRoles = Set.empty,
		    individuals = Set.empty,
		    axioms = Set.empty,
		    namespaceMap = Map.empty
		  }

emptySign :: ID -> Sign
simpleSign ontoID = 
            Sign { ontologyID = ontoID, 
                  concepts = Set.empty,
		   primaryConcepts = Set.empty,
		   datatypes = Set.empty,
		   indValuedRoles = Set.empty,
		   dataValuedRoles = Set.empty,
		   individuals = Set.empty,
		   axioms = Set.empty,
		   namespaceMap = Map.empty
		 }

diffSig :: Sign -> Sign -> Sign
diffSig a b = 
    a { concepts = concepts a `Set.difference` concepts b
      , primaryConcepts = primaryConcepts a `Set.difference` primaryConcepts b
      , datatypes = datatypes a `Set.difference` datatypes b
      , indValuedRoles = indValuedRoles a `Set.difference` indValuedRoles b   
      , dataValuedRoles = dataValuedRoles a `Set.difference` dataValuedRoles b
      , individuals = individuals a `Set.difference` individuals b
      , axioms = axioms a `Set.difference` axioms b
      }

addSign :: Sign -> Sign -> Sign
insertSign toIns totalSign =
    totalSign { concepts = Set.union (concepts totalSign) (concepts toIns),
		primaryConcepts = Set.union (primaryConcepts totalSign) (primaryConcepts toIns),
		datatypes = Set.union (datatypes totalSign) (datatypes toIns),
		indValuedRoles = Set.union (indValuedRoles totalSign) (indValuedRoles toIns),
		dataValuedRoles = Set.union (dataValuedRoles totalSign) (dataValuedRoles toIns),
		individuals = Set.union (individuals totalSign) (individuals toIns),
		axioms = Set.union (axioms totalSign) (axioms toIns)
	      }

{- a Set.isSubsetOf b && -}

isSubSign :: Sign -> Sign -> Bool
isSubSign a b = True

