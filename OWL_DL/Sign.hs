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
import qualified Common.Lib.Set as Set

data Sign = Sign
            {  concepts :: Set.Set URIreference -- ^ a set of classes
              , primaryConcepts :: Set.Set URIreference -- ^ a set of subclasses
              ,indValuedRoles :: Set.Set URIreference -- ^ a set of object property
              ,dataValuedRoles :: Set.Set URIreference -- ^ a set of data property
              ,individuals :: Set.Set IndividualID  -- ^ a set of individual
              -- ^ a set of axioms of subconceptrelations, domain an drenge 
              -- ^of roles, functional roles and concept membership
              ,axioms :: Set.Set SignAxiom  
            } deriving (Show,Eq,Ord)

data SignAxiom = Subconcept ClassID ClassID       -- subclass, superclass
               | RoleDomain RoleID ID
               | RoleRange  RoleID ID
               | FuncRole   RoleID
               | Conceptmembership IndividualID ClassID
                 deriving (Show,Eq,Ord)

data RoleID = IVP IndividualvaluedPropertyID 
            | DVP DatavaluedPropertyID
              deriving (Show,Eq,Ord)

type ID = URIreference          -- for universal ID

data Sentence = OWLAxiom Axiom                       
              | OWLFact Fact
                deriving (Show,Eq,Ord)

simpleSign :: ID -> Sign
simpleSign ontoID = 
            Sign { concepts = Set.insert ontoID Set.empty,
		   primaryConcepts = Set.empty,
		   indValuedRoles = Set.empty,
		   dataValuedRoles = Set.empty,
		   individuals = Set.empty,
		   axioms = Set.empty
		 }