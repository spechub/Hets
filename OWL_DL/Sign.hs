{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2005
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Signatures for modal logic (OWL_DL).
-}

module OWL_DL.Sign where

import OWL_DL.AS
import qualified Common.Lib.Set as Set

data OWL_DLSign = OWL_DLSign
            {  concepts :: Set.Set Axiom      -- ^ a set of classes
              ,subConcepts :: Set.Set Axiom   -- ^ a set of subclasses
              ,indValuedRoles :: Set.Set Axiom  -- ^ a set of object property
              ,dataValuedRoles :: Set.Set Axiom -- ^ a set of data property
              ,individuals :: Set.Set IndividualID  -- ^ a set of individual
              -- ^ a set of axioms of subconceptrelations, domain an drenge 
              -- ^of roles, functional roles and concept membership
              ,axioms :: Set.Set SignAxiom  
            }

data SignAxiom = Subconcept ClassID ClassID       -- subclass, superclass
               | RoleDomain RoleID ID
               | RoleRange  RoleID ID
               | FuncRole   RoleID
               | Conceptmembership IndividualID ClassID

data RoleID = IVP IndividualValuedPropertyID 
            | DVP DataValuedPropertyID

type ID = URIreference          -- for universal ID

data OWL_DLSentence = ConceptAxiom Axiom
                    | RoleAxiom Axiom
                    | FactSen Fact

-- data Concept = 

-- data Role = 

-- data Fact 
