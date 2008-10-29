{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2004-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

static analysis of basic specifications for OWL 1.1.
-}

module OWL.StaticAnalysis (basicOWLAnalysis) where

import OWL.Namespace
import OWL.Sign
import OWL.AS

import qualified Data.Set as Set
import qualified Data.Map as Map

import Common.AS_Annotation
import Common.Result
import Common.GlobalAnnotations
import Common.ExtSign
import Common.Utils (nubOrd)

import Data.Char (toLower)

-- | static analysis of ontology with incoming sign.
basicOWLAnalysis ::
    (OntologyFile, Sign, GlobalAnnos) ->
        Result (OntologyFile, ExtSign Sign (), [Named Sentence])
basicOWLAnalysis (ofile, inSign, ga) =
 if isEmptyOntologyFile ofile then
     fail "An empty OntologyFile has been found."
   else
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
                    ++ (show ofile) ++ "\n" ++ show u)

  where -- static analysis with changed namespace base of inSign.
        anaOntologyFile :: Sign -> OntologyFile
                    -> Result (OntologyFile, Sign, [Named Sentence])
        anaOntologyFile inSign' (OntologyFile ns' on) =
            case anaAxioms ga (inSign' {ontologyID = uri on}) ns'
                  (OntologyFile ns' (Ontology (uri on) [] [] []))
                  (nubOrd $ axiomsList on) of
              Result dgs (Just (onto, sign, sents)) ->
                  let c = Set.toList $ concepts sign
                      np = getNonPrimaryConcept $ axiomsList on
                      sign' = sign { primaryConcepts = Set.difference
                                       (Set.fromList c) (Set.fromList np)
                                   }
                      sents' = nubOrd sents
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
            Map.delete "owl11" (Map.delete "owl" (Map.delete "xsd"
               (Map.delete "rdf" (Map.delete "rdfs"
                  (Map.delete "xml" namespace)))))

-- | concat the current result with total result
-- | first parameter is an result from current directive
-- | second parameter is the total result
concatResult :: Result (OntologyFile,Sign,[Named Sentence])
             -> Result (OntologyFile,Sign,[Named Sentence])
             -> Result (OntologyFile,Sign,[Named Sentence])
concatResult (Result diag1 maybeRes1) (Result diag2 maybeRes2) =
    case maybeRes1 of
    Nothing ->
        case maybeRes2 of
        Nothing -> Result (diag2++diag1) Nothing
        _ -> Result (diag2++diag1) maybeRes2
    Just (ontoF1, _, namedSen1) ->
        case maybeRes2 of
         Nothing -> Result (diag2++diag1) maybeRes1
         Just (ontoF2, inSign2, namedSen2) ->
             let
                 accSign = inSign2 -- insertSign inSign1 inSign2
                 namedSen = namedSen1 ++ namedSen2
                 onto = integrateOntologyFile ontoF1 ontoF2
             in Result (diag2 ++ diag1)
                    (Just (onto, accSign, namedSen))

mkDefSen :: String -> Sentence -> Named Sentence
mkDefSen nam sen = (makeNamed nam sen) { isDef = True }

negPrefix :: PositiveOrNegative -> String
negPrefix ty = case ty of
    Positive -> ""
    Negative -> "negative_"

-- | static analyse of all Axoms of an ontology base of functional
-- | style syntax (see OWL\/OWL\/FFS.hs), ignores all imports and
-- | Annotations
-- Try to store the %implied in simpAnno of Named-struction.
anaAxioms :: GlobalAnnos -> Sign -> Namespace -> OntologyFile -> [Axiom]
            -> Result (OntologyFile,Sign,[Named Sentence])
anaAxioms _ _ _ _ [] = Result [] Nothing
anaAxioms ga inSign ns ontologyF@(OntologyFile _ onto) (axiom:rest) =
 case axiom of
  EntityAnno (EntityAnnotation _ entity _) ->  -- no idee
       let accSign =  getDeclFromEntity entity inSign
       in concatResult (Result [] (Just (ontologyF, accSign, [])))
                   (anaAxioms ga accSign ns ontologyF rest)
  PlainAxiom anno paxiom -> case paxiom of
   SubClassOf sub super  ->
       let ax = axioms inSign
           c = (getClassFromDescription sub) ++
                (getClassFromDescription super)
           namedSent = findImplied anno
                        (makeNamed (printDescForSentName sub
                                  ++ "_SubClassOf_"
                                  ++ printDescForSentName super)
                            $ OWLAxiom axiom)
           accSign = inSign {concepts =
                              Set.union (Set.fromList c) (concepts inSign)
                            ,axioms =
                              Set.insert (Subconcept sub super) ax
                            }
       in concatResult (Result [] (Just (ontologyF{ontology =
              onto{axiomsList = axiomsList onto ++ [axiom]}},
              accSign, [namedSent])))
                (anaAxioms ga accSign ns ontologyF rest)
   EquivOrDisjointClasses Equivalent descList ->
     let clazz : equiv = descList in case clazz of
      OWLClass _ ->
       let c = foldl (++) [] $ map getClassFromDescription descList
           namedSent = findImplied anno
                         (makeNamed (printDescForSentName clazz
                                  ++ "_EquivalentClasses_["
                                  ++ (foldr (\x y -> x++" "++" "++y) "]" $
                                          map printDescForSentName equiv))
                            $ OWLAxiom axiom)
           accSign = inSign {concepts =
                                 Set.union (Set.fromList c) (concepts inSign)
                            }
       in concatResult (Result [] (Just (ontologyF{ontology =
              onto{axiomsList = axiomsList onto ++ [axiom]}},
              accSign, [namedSent])))
                (anaAxioms ga accSign ns ontologyF rest)
      _ -> let reAnaAxiom = PlainAxiom anno $ EquivOrDisjointClasses
                            Equivalent (equiv ++ [clazz])
           in anaAxioms ga inSign ns ontologyF (reAnaAxiom:rest)
   EquivOrDisjointClasses Disjoint descList ->
       let clazz = head descList
           equiv = tail descList
           c = foldl (++) [] $ map getClassFromDescription descList
           namedSent = findImplied anno
                         (makeNamed (printDescForSentName clazz
                                  ++ "_DisjointClasses_["
                                  ++(foldr (\x y -> x++" "++" "++y) "]" $
                                          map printDescForSentName equiv))
                        $ OWLAxiom axiom)

           accSign = inSign {concepts =
                                 Set.union (Set.fromList c) (concepts inSign)
                            }
       in concatResult (Result [] (Just (ontologyF {ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}},
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest)
   DisjointUnion cid descList ->
       let c = cid:(foldl (++) [] $
                            map getClassFromDescription descList)

           accSign = inSign {concepts =
                                 Set.union (Set.fromList c) (concepts inSign)
                            }
           namedSent = findImplied anno
                         (makeNamed (printQN cid
                                  ++ "_DisjointUnion_["
                                  ++ (foldr (\x y -> x++" "++" "++y) "]" $
                                          map printDescForSentName descList))
                            $ OWLAxiom axiom)

       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}},
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest)
           -- ObjectPropertyAxiom
   SubObjectPropertyOf subObjProp objProp ->
       let r = (getObjRoleFromExpression objProp):
                (getObjRoleFromSubExpression subObjProp)

           accSign = inSign {indValuedRoles =
                                 Set.union (Set.fromList r)
                                        (indValuedRoles inSign)
                            }
           namedSent = findImplied anno
                         (makeNamed (printSubOExp subObjProp
                                     ++ "_SubObjectPropertyOf_"
                                     ++ printOExp objProp)
                              $ OWLAxiom axiom)

       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}},
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest)
   EquivOrDisjointObjectProperties ty objPropExps ->
       let prop = head objPropExps
           equiv = tail objPropExps
           r = map getObjRoleFromExpression objPropExps
           accSign = inSign {indValuedRoles =
                                  Set.union (Set.fromList r)
                                         (indValuedRoles inSign)
                            }
           namedSent = findImplied anno
                         (makeNamed (printOExp prop
                                 ++ "_IndividualValued"
                                     ++ show ty ++ "Properties_["
                                 ++ ((foldr (\x y -> x ++ "  " ++ y) "]" $
                                          map printOExp equiv)))
                              $ OWLAxiom axiom)
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}},
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest)
   ObjectPropertyDomainOrRange ty opExp desc ->
       let (rr, rname) = case ty of
             ObjDomain -> (RDomain, "_objectPropertyDomain_")
             ObjRange -> (RIRange, "_objectPropertyRange_")
           roleDomain = Role (DomainOrRange rr desc) opExp
           ax = axioms inSign
           accSign = inSign {axioms =
                              Set.insert roleDomain ax
                            }
           namedSent = findImplied anno
                         (makeNamed (printOExp opExp
                                 ++ rname)
                              $ OWLAxiom axiom)
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}},
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest)
   InverseObjectProperties opExp1 opExp2 ->
       let r = (getObjRoleFromExpression opExp1):
                (getObjRoleFromExpression opExp2):[]
           accSign = inSign {indValuedRoles =
                                 Set.union (Set.fromList r)
                                        (indValuedRoles inSign)
                            }
           namedSent = findImplied anno
                         (makeNamed (printOExp opExp1
                                     ++ "_InverseObjectProperty_"
                                     ++ printOExp opExp2)
                              $ OWLAxiom axiom)
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}},
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest)
   ObjectPropertyCharacter ch opExp ->
       let rname = map toLower (show ch) ++ "_object_property"
           accSign = case ch of
             Symmetric -> inSign
             Asymmetric -> inSign
             _ -> let
               funcRole = case ch of
                        Reflexive -> RefRole
                        Irreflexive -> RefRole
                        _ -> FuncRole
               r = getObjRoleFromExpression opExp
               ax = axioms inSign
               fr = Role (FuncProp (funcRole, IRole)) opExp
               in inSign {indValuedRoles = Set.insert r
                                              (indValuedRoles inSign)
                            ,axioms = Set.insert fr ax
                            }
           namedSent = findImplied anno
                         (mkDefSen rname $ OWLAxiom axiom)
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}},
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest)
     -- DataPropertyAxiom
   SubDataPropertyOf dpExp1 dpExp2 ->
       let r = dpExp1:dpExp2:[]
           accSign = inSign {dataValuedRoles =
                                 Set.union (Set.fromList r)
                                        (dataValuedRoles inSign)
                            }
           namedSent = findImplied anno
                         (makeNamed (printQN dpExp1
                                     ++ "_SubDataPropertyOf_"
                                     ++ printQN dpExp2)
                              $ OWLAxiom axiom)
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}},
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest)
   EquivOrDisjointDataProperties ty r ->
       let dpExp1 : dpExp2 : dpList = r
           accSign = inSign {dataValuedRoles =
                                 Set.union (Set.fromList r)
                                        (dataValuedRoles inSign)
                            }
           namedSent = findImplied anno
                         (makeNamed (printQN dpExp1
                                  ++ "_" ++ show ty ++ "_DataPropertyOf_"
                                  ++ printQN dpExp2
                                 ++ (foldl (\x y -> x++" "++y)
                                        "" $ map printQN dpList))
                              $ OWLAxiom axiom)
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}},
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest)
   DataPropertyDomainOrRange ddr dpExp ->
       let (dataPart, tyname) = case ddr of
              DataDomain desc -> (DomainOrRange DDomain desc, "Domain")
              DataRange dr -> (RDRange dr, "Range")
           dataSen = Data dataPart dpExp
           ax = axioms inSign
           accSign = inSign {axioms =
                              Set.insert dataSen ax
                            }
           namedSent = findImplied anno
                         (makeNamed ("DataProperty_" ++ tyname)
                          $ OWLAxiom axiom)
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}}
                                        , accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest)
   FunctionalDataProperty dpExp ->
       let _isImp = isToProve anno
           fr = Data (FuncProp ()) dpExp
           accSign = inSign { dataValuedRoles = Set.insert dpExp
                                     (dataValuedRoles inSign),
                              axioms = Set.insert fr (axioms inSign)
                            }
           namedSent = findImplied anno
                         (mkDefSen "functional_data_property"
                                               $ OWLAxiom axiom)
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}},
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest)
   -- Fact
   SameOrDifferentIndividual ty indList ->
       let ind1 : iList = indList
           accSign = inSign { individuals =
                                  Set.union (Set.fromList indList)
                                         (individuals inSign)
                            }
           namedSent = findImplied anno
                         (mkDefSen (printQN ind1
                                 ++ "_" ++ show ty ++ "Individual_"
                                 ++ (foldl (\x y -> x ++ " " ++ y)
                                        "" $ map printQN iList))
                          $ OWLFact axiom)
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}},
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest)
   ClassAssertion indUri _ ->         -- no idee
       let
           accSign = inSign { individuals = Set.insert indUri
                                            (individuals inSign)}
           namedSent = findImplied anno
                         (mkDefSen  "class_assertion"
                                 $ OWLFact axiom)
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}},
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest)
   ObjectPropertyAssertion (Assertion _ ty sourceID targetID) -> -- no idee
       let accSign = inSign { individuals = Set.insert sourceID
                                            (Set.insert targetID
                                            (individuals inSign))}
           namedSent = findImplied anno
                         (mkDefSen (negPrefix ty ++ "objectProperty_assertion")
                                                $ OWLFact axiom)
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}},
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest)
   DataPropertyAssertion (Assertion _ ty sourceID _) ->      -- no idee
       let
           accSign = inSign { individuals = Set.insert sourceID
                                            (individuals inSign)}
           namedSent = findImplied anno
                         (mkDefSen (negPrefix ty ++ "dataProperty_assertion")
                                                 $ OWLFact axiom)
       in concatResult (Result [] (Just (ontologyF{ontology=
              onto{axiomsList = axiomsList onto ++ [axiom]}},
              accSign, [namedSent])))
              (anaAxioms ga accSign ns ontologyF rest)
   Declaration entity ->
       let accSign = getDeclFromEntity entity inSign
       in concatResult (Result [] (Just (ontologyF, accSign, [])))
                   (anaAxioms ga accSign ns ontologyF rest)
  {-
       let namedSent = mkDefSen "Description_entityAnnotation"
                                  $ OWLFact axiom
       in concatResult (Result [] (Just (ontologyF{ontology=
                   onto{axiomsList = axiomsList onto ++ [axiom]}},
                   inSign, [namedSent])))
                   (anaAxioms ga inSign ns ontologyF rest)
  -}


  where getDeclFromEntity :: Entity -> Sign -> Sign
        getDeclFromEntity (Entity ty u) s =
            case ty of
              Datatype ->
                  let dt = datatypes s
                  in s { datatypes = Set.insert u dt}
              OWLClassEntity ->
                  let c = concepts s
                  in s { concepts = Set.insert u c}
              ObjectProperty ->
                  let ind = indValuedRoles s
                  in s { indValuedRoles = Set.insert u ind}
              DataProperty ->
                  let d = dataValuedRoles s
                  in s { dataValuedRoles = Set.insert u d}
              Individual ->
                  let i = individuals s
                  in s { dataValuedRoles = Set.insert u i}

-- | if CASL_Sort == false then the concept is not primary
getNonPrimaryConcept :: [Axiom] ->  [ClassID]
getNonPrimaryConcept [] = []
getNonPrimaryConcept (h:r) =
    case h of
      EntityAnno (EntityAnnotation _ (Entity OWLClassEntity curi) annos) ->
          if isCASL_SortFalse annos then
              curi:(getNonPrimaryConcept r)
              else getNonPrimaryConcept r
      _ -> getNonPrimaryConcept r
      where isCASL_SortFalse [] = False
            isCASL_SortFalse (f:s) =
                case f of
                  ExplicitAnnotation annoUri cons ->
                      if localPart annoUri == "CASL_Sort" then
                          case cons of
                            Constant lexi (Typed _) ->
                                if lexi == "false" then
                                    True
                                  else False
                            _ -> error ("incorrect type of CASL_Sort by:"
                                       ++ show h)
                        else isCASL_SortFalse s
                  _ -> isCASL_SortFalse s

getClassFromDescription :: Description -> [OwlClassURI]
getClassFromDescription desc =
    case desc of
      OWLClass clazz -> [clazz]
      ObjectJunction _ descList ->
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
findImplied :: [OWL.AS.Annotation] -> Named Sentence
            -> Named Sentence
findImplied anno sent
    | isToProve anno = sent {isAxiom = False
                            ,isDef = False
                            ,wasTheorem = False}
    | otherwise = sent {isAxiom = True}

isToProve :: [OWL.AS.Annotation] -> Bool
isToProve [] = False
isToProve (anno:r) =
    case anno of
      ExplicitAnnotation auri (Constant value (Typed _)) ->
          if localPart auri == "Implied" then
             if value == "true" then
                 True
               else False
            else isToProve r
      _ -> isToProve r
