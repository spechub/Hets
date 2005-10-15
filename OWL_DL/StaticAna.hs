{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2004-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  portable

-}


module OWL_DL.StaticAna where

import OWL_DL.Sign
import OWL_DL.AS
import Text.XML.HXT.DOM.XmlTreeTypes
import Common.Id
import qualified Common.Lib.Set as Set
import Common.AS_Annotation
import Common.Result
import Common.GlobalAnnotations
import OWL_DL.Namespace
-- import Debug.Trace

-- | static analysis of ontology with incoming sign.
basicOWL_DLAnalysis :: 
    (Ontology, Sign, GlobalAnnos) ->
        Result (Ontology,Sign,Sign,[Named Sentence])
basicOWL_DLAnalysis (ontology@(Ontology _ _ ns), inSign, ga) =
    let (integNamespace, transMap) = 
            integrateNamespaces (namespaceMap inSign) ns
        ontology' = renameNamespace transMap ontology
        Result diags1 (Just (onto, accSign, namedSen)) = 
            anaOntology (inSign {namespaceMap = integNamespace}) ontology'
        diffSign = diffSig accSign inSign
    in  Result diags1 $ Just (onto, diffSign, accSign, namedSen)
   
  where -- static analysis with changed namespace base of inSign.
        anaOntology :: Sign -> Ontology
                    -> Result (Ontology,Sign,[Named Sentence]) 
        anaOntology inSign' ontology' =
            case ontology' of
            Ontology (Just ontoID) directives ns' ->
                anaDirective ga (inSign' {ontologyID = ontoID}) 
                                 (Ontology (Just ontoID) [] ns') directives
            Ontology Prelude.Nothing directives ns' ->
                anaDirective ga (inSign' {ontologyID = nullID}) 
                                 (Ontology Prelude.Nothing [] ns') directives
                          
-- | concat the current result with total result 
-- | first parameter is an result from current directive
-- | second parameter is the total result
concatResult :: Result (Ontology,Sign,[Named Sentence]) 
             -> Result (Ontology,Sign,[Named Sentence]) 
             -> Result (Ontology,Sign,[Named Sentence]) 
concatResult (Result diag1 maybeRes1) (Result diag2 maybeRes2) =
    case maybeRes1 of
    Prelude.Nothing -> 
        case maybeRes2 of 
        Prelude.Nothing -> Result (diag2++diag1) Prelude.Nothing
        _ -> Result (diag2++diag1) maybeRes2
    Just (onto1, _, namedSen1) -> 
        case maybeRes2 of
         Prelude.Nothing -> Result (diag2++diag1) maybeRes1
         Just (onto2, inSign2, namedSen2) ->
             let
                 accSign = inSign2 -- insertSign inSign1 inSign2
                 namedSen = namedSen2 ++ namedSen1
                 ontology = integrateOntology onto1 onto2
             in Result (diag2 ++ diag1) 
                    (Just (ontology, accSign, namedSen))

-- | static analyse of all directives of an ontology base of abstact syntax
-- | (see OWL_DL/AS.hs)
anaDirective :: GlobalAnnos -> Sign -> Ontology -> [Directive]
                -> Result (Ontology,Sign,[Named Sentence])
anaDirective _ _ _ [] = initResult
anaDirective ga inSign onto@(Ontology mID direc ns) (directiv:rest) = 
  case directiv of
    Ax clazz@(Class cId _ Partial _ _) ->
     let (isPrimary, diags1) = checkPrimaryConcept clazz
     in if null diags1 then
	   if isPrimary then        -- primary concept
	     let c = concepts inSign
		 pc = primaryConcepts inSign
		 accSign = inSign { concepts = Set.insert cId c,
				    primaryConcepts = Set.insert cId pc}
	     in  concatResult (Result [] (Just (onto, accSign, [])))
		     (anaDirective ga accSign onto rest)
	    else let c = concepts inSign      -- normal concept
		     accSign = inSign {concepts = Set.insert cId c}
	         in  concatResult (Result [] (Just (onto, accSign, [])))
			 (anaDirective ga accSign onto rest)
	  else concatResult (Result diags1 Prelude.Nothing)
		       (anaDirective ga inSign onto rest)
    Ax clazz@(Class cId _ Complete _ descs) -> 
     let (isPrimary, diags1) = checkPrimaryConcept clazz
     in if null diags1 then
	   if isPrimary then        -- primary concept
	     let c = concepts inSign
		 pc = primaryConcepts inSign
		 accSign = inSign { concepts = Set.insert cId c,
				    primaryConcepts = Set.insert cId pc}
                 nsent = sentOfClass cId descs
	     in  if null nsent then
	            concatResult (Result [] (Just (onto, accSign, [])))
		     (anaDirective ga accSign onto rest)
                  else 		 
		    concatResult (Result []     
   -- ontology hier saves alle directives which are as sentences in theory
			       (Just (Ontology mID (direc ++ [directiv]) ns, 
					       accSign, nsent)))
			       (anaDirective ga accSign onto rest)
	    else let c = concepts inSign      -- normal concept
		     accSign = inSign {concepts = Set.insert cId c}
                     nsent = sentOfClass cId descs
	         in if null nsent then
		       concatResult (Result [] (Just (onto, accSign, [])))
					(anaDirective ga accSign onto rest) 
                     else 
                      concatResult        
		       (Result [] (Just (Ontology mID (direc ++ [directiv]) ns,
							accSign, nsent)))
		       (anaDirective ga accSign onto rest)
          -- if Sort definition ist error, ignored this concept...
	  else concatResult (Result diags1 Prelude.Nothing)
		       (anaDirective ga inSign onto rest)
    -- Enumerate is not primary, also "cid owl:oneOf [individualID]"
    Ax ec@(EnumeratedClass cId _ _ _) ->   
        let c = concepts inSign
	    accSign = inSign {concepts = Set.insert cId c}
            nsent   = [NamedSen { senName = (printQN cId) 
				        ++ "_oneOf_",
				 isAxiom = True,
				 isDef   = True,
				 sentence = OWLAxiom ec
			       }]
        in  concatResult (Result [] 
			  (Just (Ontology mID (direc ++ [directiv]) ns, 
					       accSign, nsent)))
			 (anaDirective ga accSign onto rest)      
    Ax dc@(DisjointClasses des1 des2 deses) ->
      let Result diags1 maybeRes = checkConcept (des1:des2:deses) inSign
      in  case maybeRes of
          Just _ -> 
            let namedSent = NamedSen { senName = (printDescForSentName des1) 
                                              ++ "_DisjointClasses_"
                                              ++ (printDescForSentName des2),
                                       isAxiom = True,  
                                       isDef = False,
                                       sentence = OWLAxiom dc
                                     }
            in  concatResult (Result diags1 
                              (Just (Ontology mID (direc ++ [directiv]) ns, 
                                     inSign, [namedSent])))
                    (anaDirective ga inSign onto rest)  
          _ -> concatResult (Result diags1 Prelude.Nothing) 
                   (anaDirective ga inSign onto rest)
    Ax ec@(EquivalentClasses des1 deses) ->
      let Result diags1 maybeRes = checkConcept (des1:deses) inSign
      in  case maybeRes of 
          Just _ -> 
	    let namedSent = 
		    NamedSen { senName = (printDescForSentName des1)
			 ++ "_EquivalentClasses_" 
                         ++ (if length deses == 1 then 
			        printDescForSentName $ head deses
			        else ""),
			       isAxiom = True,	
			       isDef = False,
			       sentence = OWLAxiom ec
			     }
	    in  concatResult (Result diags1 
			       (Just (Ontology mID (direc ++ [directiv]) ns,
				      inSign, [namedSent])))
	             (anaDirective ga inSign onto rest)
 	  _ -> concatResult (Result diags1 Prelude.Nothing) 
	           (anaDirective ga inSign onto rest)
    Ax (SubClassOf des1@(DC cid1) des2@(DC cid2)) ->
      let Result diags1 maybeRes = checkConcept (des1:des2:[]) inSign
      in  case maybeRes of 
          Just _ -> 
              let ax = axioms inSign
                  accSign = inSign { axioms = 
                                      Set.insert (Subconcept cid1 cid2) ax}
              in  concatResult (Result diags1
                                (Just (onto, accSign, [])))
                      (anaDirective ga accSign onto rest)
          _ -> concatResult (Result diags1 Prelude.Nothing) 
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
	    roleRangesAndDomains = foldDRange dpId ranges roleDomains
	    accSign = if isFunc then
		         inSign { dataValuedRoles = Set.insert dpId dvr,
				  axioms = Set.insert (FuncRole (DRole, dpId)) 
				                      roleRangesAndDomains
				}
			 else inSign { dataValuedRoles = Set.insert dpId dvr,
				       axioms = roleRangesAndDomains
				     }
        in concatResult ( Result [] (Just (onto, accSign, [])))
                  (anaDirective ga accSign onto rest)  
    Ax op@(ObjectProperty ivId _ _ _ m_inv isSmy maybeFunc domains ranges)->
        let ivr = indValuedRoles inSign
	    ax = axioms inSign
	    roleDomains = foldDomain ivId domains ax
	    roleRangesAndDomains = foldIRange ivId ranges roleDomains
	    accSign = case maybeFunc of
			 Just Functional ->
			     inSign { indValuedRoles = Set.insert ivId ivr,
				      axioms = 
				          Set.insert (FuncRole (IRole,ivId)) 
				                           roleRangesAndDomains
				    }
			 Just Functional_InverseFunctional -> 
			     inSign { indValuedRoles = Set.insert ivId ivr,
				      axioms = 
				         Set.insert (FuncRole (IRole, ivId)) 
				                           roleRangesAndDomains
				    }
			 _ ->
			     inSign { indValuedRoles = Set.insert ivId ivr,
				       axioms = roleRangesAndDomains
				     }
	    namedSent = case maybeFunc of
			Just Functional                   -> []
			-- Just Functional_InverseFunctional -> []
			_                                 ->
			  case m_inv of
			  Prelude.Nothing ->
			      if not isSmy then 
				 []
				 else
				 [NamedSen { senName = 
					 "individual_valued_role",
					     isAxiom = True,
					     isDef = True,
					     sentence = OWLAxiom op
					   } ]
			  _ -> [NamedSen { senName = 
					    "inverse_individual_valued_role",
					    isAxiom = True,
					    isDef = True,
					    sentence = OWLAxiom op
					  } ]
        in concatResult ( Result [] (Just (onto, accSign, namedSent)))
                  (anaDirective ga accSign onto rest)  
    Ax (AnnotationProperty apid _) -> 
        let accSign = inSign { annotationRoles = 
                                    Set.insert apid (annotationRoles inSign)
                             }
        in  concatResult (Result [] (Just (onto, accSign, [])))
	        (anaDirective ga accSign onto rest) 
    Ax (OntologyProperty _ _ ) ->
    {-  ontologyProperty shoud be not shown in theory.
	let namedSent = NamedSen { senName = "OntologyProperty",	
				   isAxiom = True,
				   isDef = True,
				   sentence = OWLAxiom op
				 }
        in concatResult (Result [] (Just (Ontology mID (direc++[directiv]) ns,
					  inSign, [namedSent])))
    -}
	        (anaDirective ga inSign onto rest) 
    Ax dep@(DEquivalentProperties pid1 pid2 pids) -> 
      let Result diags1 maybeRes = checkDRole (pid1:pid2:pids) inSign
      in  case maybeRes of
          Just _ -> 
              let namedSent = 
                      NamedSen { senName = (printQN pid1)
                                    ++ "_DataValuedEquivalentProterties_"
                                    ++ (printQN pid2),
                                 isAxiom = True,
                                 isDef = False,
                                 sentence = OWLAxiom dep
                               }
              in  concatResult (Result [] 
                                (Just (Ontology mID (direc ++ [directiv]) ns,
                                       inSign, [namedSent])))
                      (anaDirective ga inSign onto rest) 
          _ -> concatResult (Result diags1 Prelude.Nothing) 
                   (anaDirective ga inSign onto rest)
    Ax dsp@(DSubPropertyOf pid1 pid2) ->
      let Result diags1 maybeRes = checkDRole (pid1:pid2:[]) inSign
      in  case maybeRes of
          Just _ -> 
              let namedSent = 
                      NamedSen { senName = (printQN pid1)
                                    ++ "_DataValuedSubPropertyOf_"
                                    ++ (printQN pid2),  
                                 isAxiom = True,
                                 isDef = False,
                                 sentence = OWLAxiom dsp
                               }
              in  concatResult (Result [] 
                                (Just (Ontology mID (direc ++ [directiv]) ns,
                                       inSign, [namedSent])))
                      (anaDirective ga inSign onto rest)
          _ -> concatResult (Result diags1 Prelude.Nothing) 
                   (anaDirective ga inSign onto rest)  
    Ax iep@(IEquivalentProperties pid1 pid2 pids) ->
      let Result diags1 maybeRes = checkORole (pid1:pid2:pids) inSign
      in  case maybeRes of
          Just _ -> 
              let namedSent = 
                    NamedSen {senName = (printQN pid1)
                                 ++ "_IndividualValuedEquivalentProperties_"
                                 ++ (printQN pid2),
                              isAxiom = True,   
                              isDef = False,
                              sentence = OWLAxiom iep
                             }
              in   concatResult (Result [] 
                                 (Just (Ontology mID (direc ++ [directiv]) ns,
                                        inSign, [namedSent])))
                       (anaDirective ga inSign onto rest)
          _ -> concatResult (Result diags1 Prelude.Nothing) 
                   (anaDirective ga inSign onto rest)
    Ax isp@(ISubPropertyOf pid1 pid2) -> 
      let Result diags1 maybeRes = checkORole (pid1:pid2:[]) inSign
      in  case maybeRes of
          Just _ -> 
              let namedSent = 
                      NamedSen { senName = (printQN pid1)
                                     ++ "_IndividualValuedSubPropertyOf_"
                                     ++ (printQN pid2),
                                 isAxiom = True,        
                                 isDef = False,
                                 sentence = OWLAxiom isp
                               }
              in  concatResult (Result [] 
                                (Just (Ontology mID (direc ++ [directiv]) ns,
                                       inSign, [namedSent])))
                      (anaDirective ga inSign onto rest) 
          _ -> concatResult (Result diags1 Prelude.Nothing) 
                   (anaDirective ga inSign onto rest)
    Fc ind@(Indiv (Individual maybeIID _ types values)) ->
       case maybeIID of
        Prelude.Nothing ->          -- Error (Warnung): Individual without name
            let namedSent = NamedSen { senName = "Individual",  
                                       isAxiom = True, 
                                       isDef = True,
                                       sentence = OWLFact ind
                                     }
                diag = [Diag Warning "Individual without name" nullRange]
            in  concatResult (Result diag 
                              (Just (Ontology mID (direc ++ [directiv]) ns, 
                                     inSign, [namedSent])))
                (anaDirective ga inSign onto rest)
        Just iid -> 
            let oriInd = individuals inSign
            in  let (diagL, membershipSet) = msSet iid types ([], Set.empty) 
                    ax = axioms inSign 
                    accSign = 
                        inSign {individuals = Set.insert iid oriInd,
                                axioms = Set.union membershipSet ax
                               }
                    namedSent = if not $ null values then
                                   [NamedSen { senName = "Individual",  
                                               isAxiom = True, 
                                               isDef = True,
                                               sentence = OWLFact ind
                                             }]
                                   else []
                in  concatResult 
                         (Result diagL (Just (onto, accSign, namedSent)))
                         (anaDirective ga accSign onto rest) 
 
          where                                   
                msSet :: IndividualID -> [Type] 
                      -> ([Diagnosis], Set.Set SignAxiom)
                      -> ([Diagnosis], Set.Set SignAxiom)
                msSet _ [] res = res
                msSet rid (h:r) (diagL, ms) =
                    case h of
                    DC _ ->
                        let membership = Conceptmembership rid h
                        in  msSet rid r (diagL, Set.insert membership ms)
                    _ -> let membership = Conceptmembership rid h
                             diag' = mkDiag Warning 
                                       ("individual " ++ 
                                        (show rid) ++ 
                                        " is a member of complex description.")
                                       ()
                         in  msSet iid r (diagL ++ [diag'], 
                                          Set.insert membership ms)
     
    Fc si@(SameIndividual iid1 iid2 _) ->
        let namedSent = NamedSen { senName = (printQN iid1) 
                                      ++ "_SameIndividual_"
                                      ++ (printQN iid2),        
                                   isAxiom = False,
                                   isDef = True,
                                   sentence = OWLFact si
                                 }
        in  concatResult (Result [] (Just (Ontology mID (direc++[directiv]) ns,
                                           inSign, [namedSent])))
                (anaDirective ga inSign onto rest) 
    Fc di@(DifferentIndividuals iid1 iid2 _) ->
        let namedSent = NamedSen { senName = (printQN iid1)
                                     ++ "DifferentIndividuals"
                                     ++ (printQN iid2), 
                                   isAxiom = False,
                                   isDef = True,
                                   sentence = OWLFact di
                                 }
        in  concatResult (Result [] (Just (Ontology mID (direc++[directiv]) ns,
                                           inSign, [namedSent])))
                (anaDirective ga inSign onto rest) 
    _ -> concatResult initResult (anaDirective ga inSign onto rest) 
          -- erstmal ignoriere another
                        
    where foldDomain :: ID -> [Description] 
		     -> Set.Set SignAxiom -> Set.Set SignAxiom
	  foldDomain _ [] s = s
	  foldDomain rId d s = 
	      Set.insert (RoleDomain rId (map (\x -> RDomain x) d)) s

          foldDRange :: ID -> [DataRange] 
		     -> Set.Set SignAxiom -> Set.Set SignAxiom
	  foldDRange _ [] s = s
	  foldDRange rId d s =
	      Set.insert (RoleRange rId (map (\x -> RDRange x) d)) s

          foldIRange :: ID -> [Description] 
		     -> Set.Set SignAxiom -> Set.Set SignAxiom
	  foldIRange _ [] s = s
	  foldIRange rId d s =
	      Set.insert (RoleRange rId (map (\x -> RIRange x) d)) s

          -- if CASL_Sort == false then the concept is not primary
          checkPrimaryConcept :: Axiom -> (Bool,[Diagnosis])
          checkPrimaryConcept (Class cid _ _ annos _) =
              hasRealCASL_sortWithValue annos True True []
           where
            hasRealCASL_sortWithValue :: [OWL_DL.AS.Annotation] 
                                      -> Bool -> Bool 
                                      -> [Diagnosis] 
                                      -> (Bool, [Diagnosis])
            hasRealCASL_sortWithValue [] _ res diags1 = (res, diags1)
            hasRealCASL_sortWithValue 
              ((DLAnnotation aid tl):r) first res diags1 =
                  if localPart aid == "CASL_Sort" then
                    case tl of
                    TypedL (b, _) -> 
                     if first then
                        if b == "false" then 
                          hasRealCASL_sortWithValue r False False diags1
                          else if b == "true" then
                                 hasRealCASL_sortWithValue 
                                             r False True diags1
                                 else (False, 
                                       ((mkDiag Error 
                                          ("CASL_Sort error in " ++ 
                                                          (show cid))
                                          ()):diags1)
                                      )
                      else (False, 
                            ((mkDiag Error 
                                ((show cid)++" has more than two CASL_Sort")
                                ()):diags1)
                           ) 
                    _ -> hasRealCASL_sortWithValue r first res diags1
                    else  hasRealCASL_sortWithValue r first res diags1
            hasRealCASL_sortWithValue (_:r) first res diags1 = 
                      hasRealCASL_sortWithValue r first res diags1
          checkPrimaryConcept _ = (False, [])
          
          checkConcept :: [Description] -> Sign -> Result Bool
          checkConcept deses sign =
              checkDes deses sign initResult
           where
            checkDes :: [Description] -> Sign 
                            -> Result Bool -> Result Bool
            checkDes [] _ res = res
            checkDes (h:r) sign1 res1@(Result diag1 _) =
                case h of
                DC cid -> if checkClass cid sign1 then
                            checkDes r sign1 (res1 {maybeResult = Just True})
                            else let diag2 = 
                                      mkDiag Error 
                                       (show cid ++ " has not be declared.")
                                       ()
                                  in Result (diag1 ++ [diag2]) Prelude.Nothing
                UnionOf deses2 -> checkDes (r ++ deses2) sign1 res1
                IntersectionOf deses2 -> checkDes (r ++ deses2) sign1 res1
                ComplementOf des2 -> checkDes (r ++ [des2]) sign1 res1
                _ -> checkDes r sign1 res1              
          
          checkClass :: ClassID -> Sign -> Bool
          checkClass cid sign1 =
              Set.member cid (concepts sign1) 
          
          checkDRole :: [DatavaluedPropertyID] -> Sign -> Result Bool
          checkDRole roleIDs sign =
              checkDRole' roleIDs sign initResult
            where 
              checkDRole' :: [DatavaluedPropertyID] -> Sign 
                            -> Result Bool -> Result Bool
              checkDRole' [] _ res = res
              checkDRole' (h:r) sign2 res@(Result diag1 _) =
                  if Set.member h (dataValuedRoles sign2) then
                     checkDRole' r sign2 (res {maybeResult = Just True})
                     else let diag2 = mkDiag Error 
                                         (show h ++ " has not be declared.") 
                                         ()
                          in Result (diag1 ++ [diag2]) Prelude.Nothing

          checkORole :: [IndividualvaluedPropertyID] -> Sign -> Result Bool
          checkORole roleIDs sign =
              checkORole' roleIDs sign initResult
            where 
              checkORole' :: [IndividualvaluedPropertyID] -> Sign 
                            -> Result Bool -> Result Bool
              checkORole' [] _ res = res
              checkORole' (h:r) sign3 res@(Result diag1 _) =
                  if Set.member h (indValuedRoles sign3) then
                     checkORole' r sign3 (res {maybeResult = Just True})
                     else let diag2 = mkDiag Error 
                                         (show h ++ " has not be declared.") 
                                         ()
                          in Result (diag1 ++ [diag2]) Prelude.Nothing
          printDescForSentName :: Description -> String
          printDescForSentName (DC cid) = printQN cid
          printDescForSentName _ = ""

          sentOfClass :: ClassID -> [Description] -> [Named Sentence]
	  sentOfClass cId descs =
           if null descs then
	      []
             else 
	      if (length descs) > 1 then
	         [NamedSen {senName = (printQN cId) ++ 
			              "_intersectionOf_",
			    isAxiom = True,
			    isDef   = True,
			    sentence = OWLAxiom (EquivalentClasses (DC cId)
						 [IntersectionOf descs])
			   }]
		 else []

nullID :: ID
nullID = QN "" "" ""

initResult :: Result a
initResult = Result [] Prelude.Nothing

