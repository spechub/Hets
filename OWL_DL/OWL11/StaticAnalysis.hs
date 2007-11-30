{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2004-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

static analysis of basic specifications for OWL 1.1.
-}

module OWL_DL.OWL11.StaticAnalysis where

import OWL_DL.OWL11.Sign 
import OWL_DL.OWL11.FFS  
import qualified Data.Set as Set
import qualified Data.Map as Map
import Common.AS_Annotation
import Common.Result
import Common.GlobalAnnotations
import Common.ExtSign
import OWL_DL.Namespace
import Data.List (nub)

-- | static analysis of ontology with incoming sign.
basicOWL11Analysis ::
    (OntologyFile, Sign, GlobalAnnos) ->
        Result (OntologyFile, ExtSign Sign (), [Named Sentence])
basicOWL11Analysis (ofile, inSign, ga) =
    let ns = namespaces ofile
        diags1 = foldl (++) [] (map isNamespaceInImport
                         (Map.elems (removeDefault ns)))
        (integNamespace, transMap) =
            integrateNamespaces (namespaceMap inSign) ns   
        ofile' = renameNamespace transMap ofile
    in  case anaOntologyFile (inSign {namespaceMap = integNamespace}) ofile' of
        Result diags2 (Just (ontoFile, accSign, namedSen)) ->
          Result (diags1 ++ diags2) $
                        Just (ontoFile, mkExtSign accSign, namedSen)
        u  -> fail ("unknown error in static analysis. Please try again.\n"
                    ++ (show ofile) ++ show u)

  where -- static analysis with changed namespace base of inSign.
        anaOntologyFile :: Sign -> OntologyFile
                    -> Result (OntologyFile, Sign, [Named Sentence])
        anaOntologyFile inSign' (OntologyFile ns' on) =
            case anaAxioms ga (inSign' {ontologyID = uri on}) ns'
                  (OntologyFile ns' (Ontology (uri on) [] [] []))
                  (axiomsList on) of
              Result dgs (Just (onto, sign, sents)) ->
                  let c = nub $ Set.toList $ concepts sign
                      i = nub $ Set.toList $ individuals sign
                      p = nub $ Set.toList $ primaryConcepts sign
                      ir = nub $ Set.toList $ indValuedRoles sign
                      dr = nub $ Set.toList $ dataValuedRoles sign
                      sign' = sign { concepts = Set.fromList c
                                   , individuals = Set.fromList i
                                   , primaryConcepts = Set.fromList p
                                   , indValuedRoles = Set.fromList ir
                                   , dataValuedRoles = Set.fromList dr
                                   }
                      sents' = nub sents
                  in Result dgs 
                         (Just (onto, sign', sents'))
              res -> res

        oName = uri $ ontology ofile

        isNamespaceInImport :: String -> [Diagnosis]
        isNamespaceInImport iuri =
          if null iuri then []
            else
             let uri' = take ((length iuri) -1) iuri
             in  if uri' `elem` importList
                  then []
                  else
                    [mkDiag
                        Warning
                        ("\"" ++ uri' ++ "\"" ++
                                  " is not imported in ontology: " ++
                                  (show $ localPart oName))
                        ()]
        importList = (localPart oName):
                        (map localPart (importsList $ ontology ofile))

        removeDefault :: Namespace -> Namespace
        removeDefault namespace =
            Map.delete "owl" (Map.delete "xsd" (Map.delete "rdf"
                     (Map.delete "rdfs" (Map.delete "xml" namespace))))

-- | concat the current result with total result
-- | first parameter is an result from current directive
-- | second parameter is the total result
concatResult :: Result (OntologyFile,Sign,[Named Sentence])
             -> Result (OntologyFile,Sign,[Named Sentence])
             -> Result (OntologyFile,Sign,[Named Sentence])
concatResult (Result diag1 maybeRes1) (Result diag2 maybeRes2) =
    case maybeRes1 of
    Prelude.Nothing ->
        case maybeRes2 of
        Prelude.Nothing -> Result (diag2++diag1) Prelude.Nothing
        _ -> Result (diag2++diag1) maybeRes2
    Just (ontoF1, _, namedSen1) ->
        case maybeRes2 of
         Prelude.Nothing -> Result (diag2++diag1) maybeRes1
         Just (ontoF2, inSign2, namedSen2) ->
             let
                 accSign = inSign2 -- insertSign inSign1 inSign2
                 namedSen = namedSen2 ++ namedSen1
                 onto = integrateOntologyFile ontoF1 ontoF2
             in Result (diag2 ++ diag1)
                    (Just (onto, accSign, namedSen))

mkDefSen :: String -> Sentence -> Named Sentence
mkDefSen nam sen = (makeNamed nam sen) { isDef = True }


-- | static analyse of all Axoms of an ontology base of functional
-- | style syntax (see OWL_DL\/OWL11\/FFS.hs), ignores all imports and
-- | Annotations
anaAxioms :: GlobalAnnos -> Sign -> Namespace -> OntologyFile -> [Axiom]
            -> Result (OntologyFile,Sign,[Named Sentence])
anaAxioms _ _ _ _ [] = initResult
anaAxioms ga inSign ns ontologyF@(OntologyFile _ onto) (axiom:rest) =
  case axiom of
   SubClassOf _ sub super  ->
       let ax = axioms inSign
           c = (getClassFromDescription sub) ++ 
                (getClassFromDescription super)
           accSign = inSign {concepts =
                              Set.union (Set.fromList c) (concepts inSign)
                            ,axioms = 
                              Set.insert (Subconcept sub super) ax
                            }
       in concatResult (Result [] (Just (ontologyF, accSign, [])))
                (anaAxioms ga accSign ns ontologyF rest)
   EquivalentClasses _ descList ->
       let clazz = head descList
           equiv = tail descList
           c = foldl (++) [] $ map getClassFromDescription descList
           namedSent = makeNamed (printDescForSentName clazz
                                  ++ "_EquivalentClasses_["
                                  ++ (foldl (\x y -> x++" "++" "++y) "]" $ 
                                          map printDescForSentName equiv))
                            $ OWLAxiom axiom
           accSign = inSign {concepts =
                                 Set.union (Set.fromList c) (concepts inSign)
                            }
       in concatResult (Result [] (Just (ontologyF{ontology = 
              onto{axiomsList = axiomsList onto ++ [axiom]}}, 
              accSign, [namedSent])))
                (anaAxioms ga accSign ns ontologyF rest)
   DisjointClasses _ descList ->
       let clazz = head descList
           equiv = tail descList
           c = foldl (++) [] $ map getClassFromDescription descList
           namedSent = makeNamed (printDescForSentName clazz
                                  ++ "_DisjointClasses_["
                                  ++(foldl (\x y -> x++" "++" "++y) "]" $ 
                                          map printDescForSentName equiv))
                       $ OWLAxiom axiom
           accSign = inSign {concepts =
                                 Set.union (Set.fromList c) (concepts inSign)
                            }
       in concatResult (Result [] (Just (ontologyF {ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}}, 
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest)
   DisjointUnion _ cid descList ->
       let c = cid:(foldl (++) [] $
                            map getClassFromDescription descList)
           accSign = inSign {concepts =
                                 Set.union (Set.fromList c) (concepts inSign)
                            }
           namedSent = makeNamed (printQN cid
                                  ++ "_DisjointUnion_["
                                  ++ (foldl (\x y -> x++" "++" "++y) "]" $ 
                                          map printDescForSentName descList))
                            $ OWLAxiom axiom
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}}, 
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest)      
           -- ObjectPropertyAxiom 
   SubObjectPropertyOf _ subObjProp objProp ->
       let r = (getObjRoleFromExpression objProp):
                (getObjRoleFromSubExpression subObjProp)
           accSign = inSign {indValuedRoles =
                                 Set.union (Set.fromList r) 
                                        (indValuedRoles inSign)
                            }
           namedSent = makeNamed (printSubOExp subObjProp
                                     ++ "_SubObjectPropertyOf_"
                                     ++ printOExp objProp)
                              $ OWLAxiom axiom
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}}, 
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest)  
   EquivalentObjectProperties _ objPropExps ->
       let prop = head objPropExps
           equiv = tail objPropExps
           r = map getObjRoleFromExpression objPropExps
           accSign  = inSign {indValuedRoles = 
                                  Set.union (Set.fromList r) 
                                         (indValuedRoles inSign)
                            }
           namedSent = makeNamed (printOExp prop
                                 ++ "_IndividualValuedEquivalentProperties_["
                                 ++ ((foldl (\x y -> x++" "++" "++y) "]" $
                                          map printOExp equiv)))
                              $ OWLAxiom axiom
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}}, 
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest)
   DisjointObjectProperties _ objPropExps ->
       let prop = head objPropExps
           equiv = tail objPropExps
           r = map getObjRoleFromExpression objPropExps
           accSign  = inSign {indValuedRoles = 
                                  Set.union (Set.fromList r) 
                                         (indValuedRoles inSign)
                            }
           namedSent = makeNamed (printOExp prop
                                 ++ "_IndividualValuedDisjointProperties_["
                                 ++ ((foldl (\x y -> x++" "++" "++y) "]" $
                                          map printOExp equiv)))
                              $ OWLAxiom axiom
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}}, 
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest)
   ObjectPropertyDomain _ opExp desc ->
       let roleDomain = RoleDomain opExp (RDomain desc)
           ax = axioms inSign
           accSign = inSign {axioms = 
                              Set.insert roleDomain ax
                            }
       in concatResult (Result [] (Just (ontologyF, accSign, [])))
              (anaAxioms ga accSign ns ontologyF rest)
   ObjectPropertyRange _ opExp desc ->
       let roleRange = RoleRange opExp (RIRange desc)
           ax = axioms inSign
           accSign = inSign {axioms = 
                              Set.insert roleRange ax
                            }
       in concatResult (Result [] (Just (ontologyF, accSign, [])))
              (anaAxioms ga accSign ns ontologyF rest)
   InverseObjectProperties _ opExp1 opExp2 ->
       let r = (getObjRoleFromExpression opExp1):
                (getObjRoleFromExpression opExp2):[]
           accSign = inSign {indValuedRoles =
                                 Set.union (Set.fromList r) 
                                        (indValuedRoles inSign)
                            }
           namedSent = makeNamed (printOExp opExp1
                                     ++ "_InverseObjectProperty_"
                                     ++ printOExp opExp2)
                              $ OWLAxiom axiom
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}}, 
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest)
   FunctionalObjectProperty _ opExp ->
       let r = getObjRoleFromExpression opExp
           ax = axioms inSign
           accSign = inSign {indValuedRoles = Set.insert r 
                                              (indValuedRoles inSign)
                            ,axioms = Set.insert (FuncRole (IRole, opExp)) ax
                            }
           namedSent = mkDefSen "functional_object_property" 
                                               $ OWLAxiom axiom
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}}, 
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest)          
   InverseFunctionalObjectProperty _ opExp ->
       let r = getObjRoleFromExpression opExp
           ax = axioms inSign
           accSign = inSign {indValuedRoles = Set.insert r 
                                              (indValuedRoles inSign)
                            ,axioms = Set.insert (FuncRole (IRole, opExp)) ax
                            }
           namedSent = mkDefSen 
                                  "inverse_functional_object_property" 
                                  $ OWLAxiom axiom
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto++ [axiom]}}, 
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest) 
   ReflexiveObjectProperty _ opExp ->
       let r = getObjRoleFromExpression opExp
           ax = axioms inSign
           accSign = inSign {indValuedRoles = Set.insert r 
                                              (indValuedRoles inSign)
                            ,axioms = Set.insert (RefRole (IRole, opExp)) ax
                            }
           namedSent = mkDefSen 
                                  "reflexive_object_property" 
                                  $ OWLAxiom axiom
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}}, 
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest) 
   IrreflexiveObjectProperty _ opExp ->
       let r = getObjRoleFromExpression opExp
           ax = axioms inSign
           accSign = inSign {indValuedRoles = Set.insert r 
                                              (indValuedRoles inSign)
                            ,axioms = Set.insert (RefRole (IRole, opExp)) ax
                            }
           namedSent = mkDefSen 
                                  "irreflexive_object_property" 
                                  $ OWLAxiom axiom
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}}, 
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest) 
   SymmetricObjectProperty _ _ ->
       -- no idee
       let namedSent = mkDefSen "symetric_object_property"
                                 $ OWLFact axiom
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}}, 
              inSign, [namedSent])))
              (anaAxioms ga inSign ns ontologyF rest)   
   AntisymmetricObjectProperty _ _ ->
       -- no idee
       let namedSent = mkDefSen "antisymetric_object_property"
                                 $ OWLFact axiom
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}}, 
              inSign, [namedSent])))
              (anaAxioms ga inSign ns ontologyF rest)
   TransitiveObjectProperty _ opExp ->
       let r = getObjRoleFromExpression opExp
           ax = axioms inSign
           accSign = inSign {indValuedRoles = Set.insert r 
                                              (indValuedRoles inSign)
                            ,axioms = Set.insert (FuncRole (IRole, opExp)) ax
                            }
           namedSent = mkDefSen 
                                  "transitive_individual_valued_role" 
                                  $ OWLAxiom axiom
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}}, 
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest)
     -- DataPropertyAxiom 
   SubDataPropertyOf _ dpExp1 dpExp2 ->
       let r = dpExp1:dpExp2:[]
           accSign = inSign {dataValuedRoles = 
                                 Set.union (Set.fromList r) 
                                        (dataValuedRoles inSign)
                            }
           namedSent = makeNamed (printQN dpExp1
                                     ++ "_SubDataPropertyOf_"
                                     ++ printQN dpExp2)
                              $ OWLAxiom axiom
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}}, 
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest)  
   EquivalentDataProperties _ dpExpList ->
       let dpExp1 = head dpExpList
           dpExp2 = head $ tail dpExpList
           dpList = tail $ tail dpExpList
           r = dpExpList
           accSign = inSign {dataValuedRoles = 
                                 Set.union (Set.fromList r) 
                                        (dataValuedRoles inSign)
                            }
           namedSent = makeNamed (printQN dpExp1
                                  ++ "_Equivalent_DataPropertyOf_"
                                  ++ printQN dpExp2 
                                 ++ (foldl (\x y -> x++" "++y) 
                                        "" $ map printQN dpList))
                              $ OWLAxiom axiom
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}}, 
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest) 
   DisjointDataProperties _ dpExpList ->
       let dpExp1 = head dpExpList
           dpExp2 = head $ tail dpExpList
           dpList = tail $ tail dpExpList
           r = dpExpList
           accSign = inSign {dataValuedRoles = 
                                 Set.union (Set.fromList r) 
                                        (dataValuedRoles inSign)
                            }
           namedSent = makeNamed (printQN dpExp1
                                  ++ "_Disjoint_DataPropertyOf_"
                                  ++ printQN dpExp2 
                                 ++ (foldl (\x y ->x++" "++y) 
                                        "" $ map printQN dpList))
                              $ OWLAxiom axiom
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}}, 
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest) 

   DataPropertyDomain _ dpExp desc ->
       let dataDomain = DataDomain dpExp (DDomain desc)
           ax = axioms inSign
           accSign = inSign {axioms = 
                              Set.insert dataDomain ax
                            }
       in concatResult (Result [] (Just (ontologyF, accSign, [])))
              (anaAxioms ga accSign ns ontologyF rest)
   DataPropertyRange _ opExp dr ->
       let dataRange = DataRange opExp (RDRange dr)
           ax = axioms inSign
           accSign = inSign {axioms = 
                              Set.insert dataRange ax
                            }
       in concatResult (Result [] (Just (ontologyF, accSign, [])))
              (anaAxioms ga accSign ns ontologyF rest)
   FunctionalDataProperty _ dpExp ->
       let accSign = inSign { dataValuedRoles = Set.insert dpExp 
                                     (dataValuedRoles inSign),
                              axioms = Set.insert (FuncDataProp dpExp)
                                        (axioms inSign)
                            }
           namedSent = mkDefSen "functional_data_property" 
                                               $ OWLAxiom axiom
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}}, 
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest) 
   -- Fact
   SameIndividual _ indList ->
       let ind1 = head indList
           iList = tail indList
           accSign = inSign { individuals = 
                                  Set.union (Set.fromList indList) 
                                         (individuals inSign)
                            }
           namedSent = mkDefSen (printQN ind1 
                                 ++ "_SameIndividual_"
                                 ++ (foldl (\x y -> x++" "++y) 
                                        "" $ map printQN iList))
                       $ OWLFact axiom
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}}, 
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest) 
   DifferentIndividuals _ indList ->
       let ind1 = head indList
           iList = tail indList
           accSign = inSign { individuals = Set.union (Set.fromList indList) 
                                            (individuals inSign)}
           namedSent = mkDefSen (printQN ind1 
                                 ++ "_DifferentIndividual_"
                                 ++ (foldl (\x y ->x++" "++y) 
                                        "" $ map printQN iList))
                       $ OWLFact axiom
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}}, 
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest)        
   ClassAssertion _ _ _ ->         -- no idee
       let namedSent = mkDefSen  "class_assertion"
                                 $ OWLFact axiom
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}}, 
              inSign, [namedSent])))
              (anaAxioms ga inSign ns ontologyF rest) 
   ObjectPropertyAssertion _ _ _ _ ->       -- no idee
       let namedSent = mkDefSen  "object_assertion"
                                                $ OWLFact axiom
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}}, 
              inSign, [namedSent])))
              (anaAxioms ga inSign ns ontologyF rest)        
   NegativeObjectPropertyAssertion _ _ _ _ ->     -- no idee
       let namedSent = mkDefSen  "object_assertion"
                                 $ OWLFact axiom
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}}, 
              inSign, [namedSent])))
              (anaAxioms ga inSign ns ontologyF rest)  
   DataPropertyAssertion _ _ _ _ ->      -- no idee
       let namedSent = mkDefSen  "object_assertion"
                                                 $ OWLFact axiom
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}}, 
              inSign, [namedSent])))
              (anaAxioms ga inSign ns ontologyF rest) 
   NegativeDataPropertyAssertion _ _ _ _ ->      -- no idee
       let namedSent = mkDefSen "object_assertion"
                                               $ OWLFact axiom
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}}, 
              inSign, [namedSent])))
              (anaAxioms ga inSign ns ontologyF rest)        
   Declaration _ entity ->
       case entity of
         Datatype u  ->
             let dt = datatypes inSign
                 accSign = inSign { datatypes = Set.insert u dt}
             in  concatResult (Result [] (Just (ontologyF, accSign, [])))
                   (anaAxioms ga accSign ns ontologyF rest)
         OWLClassEntity u ->
             let c = concepts inSign
                 accSign = inSign { concepts = Set.insert u c}
             in  concatResult (Result [] (Just (ontologyF, accSign, [])))
                   (anaAxioms ga accSign ns ontologyF rest)
         ObjectProperty u ->
             let ind = indValuedRoles inSign
                 accSign = inSign { indValuedRoles = Set.insert u ind}
             in  concatResult (Result [] (Just (ontologyF, accSign, [])))
                   (anaAxioms ga accSign ns ontologyF rest)
         DataProperty u ->
             let d = dataValuedRoles inSign
                 accSign = inSign { dataValuedRoles = Set.insert u d}
             in  concatResult (Result [] (Just (ontologyF, accSign, [])))
                   (anaAxioms ga accSign ns ontologyF rest)             
         Individual u ->
             let i = individuals inSign
                 accSign = inSign { dataValuedRoles = Set.insert u i}
             in  concatResult (Result [] (Just (ontologyF, accSign, [])))
                   (anaAxioms ga accSign ns ontologyF rest) 
   EntityAnno _ ->      -- no idee
       let namedSent = mkDefSen
                                  "Description_entityAnnotation"
                                  $ OWLFact axiom
       in concatResult (Result [] (Just (ontologyF{ontology=
                   onto{axiomsList = axiomsList onto ++ [axiom]}}, 
                   inSign, [namedSent])))
                   (anaAxioms ga inSign ns ontologyF rest) 


-- | if CASL_Sort == false then the concept is not primary
getPrimaryConcept :: [Axiom] ->  [ClassID]
getPrimaryConcept [] = []
getPrimaryConcept (h:r) =
    case h of
      EntityAnno (EntityAnnotation _ (OWLClassEntity curi) annos) ->
          if isCASL_SortFalse annos then
              curi:(getPrimaryConcept r)
              else getPrimaryConcept r
      _ -> getPrimaryConcept r
      where isCASL_SortFalse [] = True
            isCASL_SortFalse (f:s) =
                case f of 
                  ExplicitAnnotation annoUri cons ->
                      if localPart annoUri == "CASL_Sort" then
                          case cons of
                            TypedConstant (lexi, _) ->
                                if lexi == "false" then
                                    False
                                  else True
                            _ -> error ("incorrect type of CASL_Sort by:"
                                       ++ show h)
                        else isCASL_SortFalse s
                  _ -> isCASL_SortFalse s
                      
getAllConceptsAndRoles :: Ontology 
                       -> ([OwlClassURI], [IndividualURI]
                          ,[IndividualURI], [IndividualURI])
getAllConceptsAndRoles onto = getAllConcepts' (axiomsList onto) 
                                                  ([],[],[],[])
  where getAllConcepts' [] res = res
        getAllConcepts' (h:r) res@(con, objRole, dataRole, annoRole) =
         case h of
           SubClassOf _ sub super -> 
            getAllConcepts' r (((getClassFromDescription sub) ++
             (getClassFromDescription super) ++con),objRole, dataRole, annoRole)
           EquivalentClasses _ descList -> 
               getAllConcepts' r (((foldl (++) [] $ map
                                    getClassFromDescription descList) ++ con),
                                  objRole, 
                                  dataRole, annoRole)
           DisjointClasses _  descList -> 
               getAllConcepts' r  (((foldl (++) [] $ map 
                                   getClassFromDescription descList) ++ con)
                                  ,objRole, dataRole, annoRole)
           DisjointUnion _ clazz descList -> 
               getAllConcepts' r (((clazz:(foldl (++) [] $ map 
                                   getClassFromDescription descList)) ++ con)
                                 ,objRole, dataRole, annoRole)
           Declaration _ (OWLClassEntity clazz) -> 
               getAllConcepts' r ((clazz:con)
                                 ,objRole, dataRole, annoRole)
           EntityAnno (EntityAnnotation _ (OWLClassEntity clazz) _) ->
               getAllConcepts' r ((clazz:con)
                                  ,objRole, dataRole, annoRole)
           _ -> getAllConcepts' r res


getClassFromDescription :: Description -> [OwlClassURI]
getClassFromDescription desc =
    case desc of
      OWLClass clazz -> [clazz]
      ObjectUnionOf descList -> 
              foldl (++) [] $ map getClassFromDescription descList
      ObjectIntersectionOf descList ->
              foldl (++) [] $ map getClassFromDescription descList
      ObjectComplementOf desc' -> getClassFromDescription desc'
      _ -> []

getObjRoleFromExpression :: ObjectPropertyExpression -> IndividualRoleURI
getObjRoleFromExpression opExp =
    case opExp of
       OpURI u -> u
       InverseOp objProp -> getObjRoleFromExpression objProp

getObjRoleFromSubExpression :: SubObjectPropertyExpression 
                            -> [IndividualRoleURI]
getObjRoleFromSubExpression sopExp =
    case sopExp of
      OPExpression opExp -> (getObjRoleFromExpression opExp):[]
      SubObjectPropertyChain expList ->
          map getObjRoleFromExpression expList

printDescForSentName :: Description -> String
printDescForSentName (OWLClass cid) = printQN cid
printDescForSentName _ = ""


printOExp :: ObjectPropertyExpression ->  String
printOExp opExp =
    case opExp of
      OpURI u -> printQN u
      InverseOp opExp' -> "inverse "++ printOExp opExp'

printSubOExp :: SubObjectPropertyExpression -> String
printSubOExp subOpExp =
    case subOpExp of
      OPExpression opExp -> printOExp opExp
      SubObjectPropertyChain opExpList ->
          "chain: " ++ (foldl (\x y -> x++ " " ++ " " ++y) 
                                  ""  $ map printOExp opExpList)

nullID :: ID
nullID = QN "" "" ""

initResult :: Result a
initResult = Result [] Prelude.Nothing
