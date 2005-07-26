{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2004-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  portable

-}


module OWL_DL.StaticAna where

-- import Static.DevGraph
-- import Data.Graph.Inductive.Graph
import OWL_DL.Sign
-- import OWL_DL.Logic_OWL_DL
import OWL_DL.AS
-- import OWL_DL.ReadWrite
-- import Common.DefaultMorphism
import Text.XML.HXT.DOM.XmlTreeTypes
-- import Logic.Grothendieck
-- import Common.Id
-- import List
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.AS_Annotation
import Common.Result
import Common.GlobalAnnotations
import Debug.Trace

basicOWL_DLAnalysis :: 
    (Ontology, Sign, GlobalAnnos) ->
	Result (Ontology,Sign,Sign,[Named Sentence])
basicOWL_DLAnalysis (ontology, inSign, ga) =
    let Result diags (Just (onto, accSign, namedSen)) = 
	    anaOntology ga inSign ontology
	diffSign = diffSig accSign inSign
    in  Result diags $ Just (onto, diffSign, accSign, namedSen)


anaOntology :: GlobalAnnos -> Sign -> Ontology
            -> Result (Ontology,Sign,[Named Sentence]) 
anaOntology ga inSign ontology =
    case ontology of
     Ontology (Just ontoID) directives ->
       anaDirective ga (inSign {ontologyID = ontoID}) (Ontology (Just ontoID) []) directives
     Ontology Prelude.Nothing directives ->
	anaDirective ga (inSign {ontologyID = nullID}) (Ontology Prelude.Nothing []) directives
			  
-- concat the current result with total result 
-- first result is an result from current directive
-- second result is the total result
concatResult :: Result (Ontology,Sign,[Named Sentence]) 
	     -> Result (Ontology,Sign,[Named Sentence]) 
	     -> Result (Ontology,Sign,[Named Sentence]) 
concatResult (Result diag1 maybeRes1) (Result diag2 maybeRes2) =
    case maybeRes1 of
    Prelude.Nothing -> 
	case maybeRes2 of 
	Prelude.Nothing -> Result (diag1++diag2) Prelude.Nothing
	_ -> Result (diag1++diag2) maybeRes2
    Just (onto1@(Ontology maybeID1 direc1), inSign1, namedSen1) -> 
	case maybeRes2 of
	 Prelude.Nothing -> Result (diag1++diag2) maybeRes1
	 Just ((Ontology maybeID2 direc2), inSign2, namedSen2) ->
	    if maybeID1 /= maybeID2 then
	       error "unknow error in concatResult"
	       else let -- todo: concat ontology
                        accSign = inSign2 -- insertSign inSign1 inSign2
                        namedSen = namedSen2 ++ namedSen1
                    in Result (diag2 ++ diag1) 
			 (Just (onto1, accSign, namedSen)) 

anaDirective :: GlobalAnnos -> Sign -> Ontology -> [Directive]
		-> Result (Ontology,Sign,[Named Sentence])
anaDirective _ _ _ [] = initResult
anaDirective ga inSign onto (directiv:rest) = 
  case directiv of
    Ax (Class cId _ _ _ des) -> 
	if null des then        -- primary Concept has no super concept
	   let c = concepts inSign
	       pc = primaryConcepts inSign
	       accSign = inSign { concepts = Set.insert cId c,
				  primaryConcepts = Set.insert cId pc}
	   in  concatResult (Result [] (Just (onto, accSign, [])))
		       (anaDirective ga accSign onto rest)
	  -- normal concept has super concept
	  else let c = concepts inSign
	           accSign = inSign {concepts = Set.insert cId c}
	       in  concatResult (Result [] (Just (onto, accSign, [])))
		       (anaDirective ga accSign onto rest)
    Ax (EnumeratedClass cId _ _ _) ->   -- Enumerate is not primary
        let c = concepts inSign
	    accSign = inSign {concepts = Set.insert cId c}
        in  concatResult (Result [] (Just (onto, accSign, [])))
	         (anaDirective ga accSign onto rest)      
    Ax dc@(DisjointClasses _ _ _) ->
	let namedSent = NamedSen { senName = "DisjointClasses",	
				   isAxiom = True,	
				   sentence = OWLAxiom dc
				 }
        in  concatResult (Result [] (Just (onto, inSign, [namedSent])))
	        (anaDirective ga inSign onto rest)    
    Ax ec@(EquivalentClasses _ _) ->
	let namedSent = NamedSen { senName = "EquivalentClasses",	
				   isAxiom = True,	
				   sentence = OWLAxiom ec
				 }
        in   concatResult (Result [] (Just (onto, inSign, [namedSent])))
	        (anaDirective ga inSign onto rest) 
    Ax sc@(SubClassOf _ _) ->
	let namedSent = NamedSen { senName = "SubClassOf",	
				   isAxiom = True,	
				   sentence = OWLAxiom sc
				 }
        in   concatResult (Result [] (Just (onto, inSign, [namedSent])))
	        (anaDirective ga inSign onto rest) 
    Ax (Datatype dtId _ _) -> 
	let d = datatypes inSign
            accSign = inSign {datatypes = Set.insert dtId d}
	in  concatResult (Result [] (Just (onto, accSign, [])))
	          (anaDirective ga accSign onto rest)  
    Ax (DatatypeProperty dpId _ _ _ isFunc domains ranges) ->
	let dvr = dataValuedRoles inSign
	    ax = axioms inSign
	    roleDomains = foldDomain dpId domains ax
	    roleRanges = foldDRange dpId ranges roleDomains
	    accSign = if isFunc then
		         inSign { dataValuedRoles = Set.insert dpId dvr,
				  axioms = Set.insert (FuncRole dpId) roleRanges
				}
			 else inSign { dataValuedRoles = Set.insert dpId dvr,
				       axioms = roleRanges
				     }
        in concatResult ( Result [] (Just (onto, accSign, [])))
	          (anaDirective ga accSign onto rest)  
    Ax (ObjectProperty ivId _ _ _ _ _ maybeFunc domains ranges) ->
        let ivr = indValuedRoles inSign
	    ax = axioms inSign
	    roleDomains = foldDomain ivId domains ax
	    roleRanges = foldIRange ivId ranges roleDomains
	    accSign = case maybeFunc of
		         Just Transitive -> 
			     inSign { indValuedRoles = Set.insert ivId ivr,
				      axioms = roleRanges
				    }
			 Just _ ->
			     inSign { indValuedRoles = Set.insert ivId ivr,
				      axioms = Set.insert (FuncRole ivId) roleRanges
				    }
			 _ -> inSign { indValuedRoles = Set.insert ivId ivr,
				       axioms = roleRanges
				     }
        in concatResult ( Result [] (Just (onto, accSign, [])))
	          (anaDirective ga accSign onto rest)  
    Ax ap@(AnnotationProperty _ _) -> 
	let namedSent = NamedSen { senName = "AnnotationProperty",	
				   isAxiom = True,	
				   sentence = OWLAxiom ap
				 }
        in  concatResult (Result [] (Just (onto, inSign, [namedSent])))
	        (anaDirective ga inSign onto rest) 
    Ax op@(OntologyProperty _ _ ) ->
	let namedSent = NamedSen { senName = "OntologyProperty",	
				   isAxiom = True,	
				   sentence = OWLAxiom op
				 }
        in concatResult (Result [] (Just (onto, inSign, [namedSent])))
	        (anaDirective ga inSign onto rest) 
    Ax dep@(DEquivalentProperties _ _ _) -> 
	let namedSent = NamedSen { senName = "DataValuedEquivalentProterties",	
				   isAxiom = True,	
				   sentence = OWLAxiom dep
				 }
        in  concatResult (Result [] (Just (onto, inSign, [namedSent])))
	        (anaDirective ga inSign onto rest) 
    Ax dsp@(DSubPropertyOf _ _) ->
	let namedSent = NamedSen { senName = "DataValuedSubPropertyOf",	
				   isAxiom = True,	
				   sentence = OWLAxiom dsp
				 }
        in  concatResult (Result [] (Just (onto, inSign, [namedSent])))
	        (anaDirective ga inSign onto rest)  
    Ax iep@(IEquivalentProperties _ _ _) ->
	let namedSent = NamedSen { senName = "IndividualValuedEquivalentProperties",	
				   isAxiom = True,	
				   sentence = OWLAxiom iep
				 }
        in   concatResult (Result [] (Just (onto, inSign, [namedSent])))
	        (anaDirective ga inSign onto rest) 
    Ax isp@(ISubPropertyOf _ _) -> 
	let namedSent = NamedSen { senName = "IndividualValuedSubPropertyOf",	
				   isAxiom = True,	
				   sentence = OWLAxiom isp
				 }
        in   concatResult (Result [] (Just (onto, inSign, [namedSent])))
	        (anaDirective ga inSign onto rest) 

    Fc ind@(Indiv (Individual maybeIID _ types _)) ->
       case maybeIID of
	Prelude.Nothing ->  
	    let namedSent = NamedSen { senName = "Individual",	
				       isAxiom = False,	
				       sentence = OWLFact ind
				     }
            in  concatResult (Result [] (Just (onto, inSign, [namedSent])))
	        (anaDirective ga inSign onto rest)
	Just iid -> let oriInd = individuals inSign
		    in  if length types == 1 then
			   case head types of
			     DC cid -> let cmembership = Conceptmembership iid cid
				  	   ax = axioms inSign 
					   accSign = inSign { individuals = Set.insert iid oriInd,
							    axioms = Set.insert cmembership ax
							  }
			               in  concatResult (Result [] (Just (onto, accSign, [])))
					     (anaDirective ga accSign onto rest) 
			     _  ->  concatResult (Result [] (Just (onto, (accSign' oriInd), [])))
				        (anaDirective ga (accSign' oriInd) onto rest) 
		          else concatResult (Result [] (Just (onto, (accSign' oriInd), [])))
				        (anaDirective ga (accSign' oriInd) onto rest) 
	  where accSign' oriInd= inSign { individuals = Set.insert iid oriInd}
     
    Fc si@(SameIndividual _ _ _) ->
	let namedSent = NamedSen { senName = "SameIndividual",	
				   isAxiom = False,	
				   sentence = OWLFact si
				 }
        in  concatResult (Result [] (Just (onto, inSign, [namedSent])))
	        (anaDirective ga inSign onto rest) 
    Fc di@(DifferentIndividuals _ _ _) ->
	let namedSent = NamedSen { senName = "DifferentIndividuals",	
				   isAxiom = False,	
				   sentence = OWLFact di
				 }
        in  concatResult (Result [] (Just (onto, inSign, [namedSent])))
	        (anaDirective ga inSign onto rest) 
    _ -> concatResult initResult (anaDirective ga inSign onto rest)  -- erstmal ignoriere another
 			
    where foldDomain :: ID -> [Description] 
		     -> Set.Set SignAxiom -> Set.Set SignAxiom
	  foldDomain _ [] s = s
	  foldDomain rId (h:r) s = 
	      foldDomain rId r (Set.insert (RoleDomain rId (RDomain h)) s)

          foldDRange :: ID -> [DataRange] 
		     -> Set.Set SignAxiom -> Set.Set SignAxiom
	  foldDRange _ [] s = s
	  foldDRange rId (h:r) s =
	      foldDRange rId r (Set.insert (RoleRange rId (RDRange h)) s)

          foldIRange :: ID -> [Description] 
		     -> Set.Set SignAxiom -> Set.Set SignAxiom
	  foldIRange _ [] s = s
	  foldIRange rId (h:r) s =
	      foldIRange rId r (Set.insert (RoleRange rId (RIRange h)) s)

nullID = QN "" "" ""
initResult = Result [] Prelude.Nothing