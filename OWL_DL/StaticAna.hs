{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2004-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

static analysis of basic specifications for OWL_DL.
-}

module OWL_DL.StaticAna where

import OWL_DL.Sign
import OWL_DL.AS
import qualified Data.Set as Set
import qualified Data.Map as Map
import Common.AS_Annotation
import Common.Result
import Common.GlobalAnnotations
import Common.ExtSign
import OWL_DL.Namespace
import Data.Maybe (fromJust)

-- | static analysis of ontology with incoming sign.
basicOWL_DLAnalysis ::
    (Ontology, Sign, GlobalAnnos) ->
        Result (Ontology, ExtSign Sign (), [Named Sentence])
basicOWL_DLAnalysis (ontology@(Ontology oName _ ns), inSign, ga) =
    let -- importsUriList = searchImport ontology
        diags1 = foldl (++) [] (map isNamespaceInImport
                                (Map.elems (removeDefault ns)))
        (integNamespace, transMap) =
            integrateNamespaces (namespaceMap inSign) ns
        ontology' = renameNamespace transMap ontology
    in  case anaOntology (inSign {namespaceMap = integNamespace}) ontology' of
        Result diags2 (Just (onto, accSign, namedSen)) ->
          Result (diags1 ++ diags2) $
                        Just (onto, mkExtSign accSign, namedSen)
        _  -> fail ("unknown error in static analysis. Please try again.\n" ++
                  (show $ anaOntology (inSign {namespaceMap = integNamespace})
                        ontology'))

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

        isNamespaceInImport :: String -> [Diagnosis]
        isNamespaceInImport uri =
          if null uri then []
            else
             let uri' = take ((length uri) -1) uri
             in  if uri' `elem` importList
                  then []
                  else
                    [mkDiag
                        Warning
                        ("\"" ++ uri' ++ "\"" ++
                                  " is not imported in ontology: " ++
                                  (show $ localPart $ fromJust oName))
                        ()]
        importList = (localPart $ fromJust oName):(searchImport ontology)

        searchImport :: Ontology -> [String]
        searchImport (Ontology _ directives _) = findImports directives
            where
            findImports :: [Directive] -> [String]
            findImports [] = []
            findImports (hd:rd) =
                case hd of
                Ax (OntologyProperty oid uriannos) ->
                    if localPart oid == "imports" then
                       findImports' uriannos
                       else findImports rd
                _ -> findImports rd
            findImports' :: [OWL_DL.AS.Annotation] -> [String]
            findImports' [] = []
            findImports' (ha:ra) =
                case ha of
                URIAnnotation _ qn ->
                    let nsUri = localPart qn
--  in  (take ((length nsUri) -1) nsUri):(findImports' ra)   -- remove #
                    in nsUri:(findImports' ra)
                _ -> []

        removeDefault :: Namespace -> Namespace
        removeDefault namespace =
            Map.delete "owl" (Map.delete "xsd" (Map.delete "rdf"
                     (Map.delete "rdfs" (Map.delete "xml" namespace))))

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

mkDefSen :: String -> Sentence -> Named Sentence
mkDefSen nam sen = (makeNamed nam sen) { isDef = True }

-- | static analyse of all directives of an ontology base of abstact syntax
-- | (see OWL_DL\/AS.hs)
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
            nsent   = [mkDefSen (printQN cId ++ "_oneOf_") $ OWLAxiom ec]
        in  concatResult (Result []
                          (Just (Ontology mID (direc ++ [directiv]) ns,
                                               accSign, nsent)))
                         (anaDirective ga accSign onto rest)
    Ax dc@(DisjointClasses des1 des2 deses) ->
      let Result diags1 maybeRes = checkConcept (des1:des2:deses) inSign
      in  case maybeRes of
          Just _ ->
            let namedSent = makeNamed (printDescForSentName des1
                                              ++ "_DisjointClasses_"
                                              ++ printDescForSentName des2)
                            $ OWLAxiom dc
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
            let namedSent = makeNamed (printDescForSentName des1
                                    ++ "_EquivalentClasses_"
                                    ++ (if length deses == 1 then
                                            printDescForSentName $ head deses
                                        else ""))
                            $ OWLAxiom ec
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
    Ax op@(ObjectProperty ivId p2 p3 p4 m_inv isSmy maybeFunc domains ranges)->
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
            (remake, namedSent) = case maybeFunc of
                                    -- case of inverse or transitive
                        Just Functional -> (False, [])
                        Just Transitive ->
                          let mkTransSen = mkDefSen
                                             "transitive_individual_valued_role"
                          in case m_inv of
                             Prelude.Nothing -> (False,
                               [ mkTransSen $ OWLAxiom op ])
                             _ -> (True,
                               [ mkTransSen $ OWLAxiom $
                                 ObjectProperty ivId p2 p3 p4 Prelude.Nothing
                                 isSmy maybeFunc domains ranges ])
            -- then either InverseFunction or Functional_InverseFunctional:
                        _ -> (False,
                          case m_inv of
                          Prelude.Nothing -> if not isSmy then [] else
                               [ mkDefSen "individual_valued_role"
                               $ OWLAxiom op ]
                          _ -> [ mkDefSen "inverse_individual_valued_role"
                               $ OWLAxiom op ])
        in if remake then
               concatResult ( Result [] (Just (onto, accSign, namedSent)))
                      (anaDirective ga accSign onto
                       (Ax (ObjectProperty ivId p2 p3 p4 m_inv isSmy
                             Prelude.Nothing domains ranges) : rest))
             else concatResult ( Result [] (Just (onto, accSign, namedSent)))
                      (anaDirective ga accSign onto rest)
    -- annotation properties are not yet handled.
    Ax (AnnotationProperty apid _) ->
        let accSign = inSign { annotationRoles =
                                    Set.insert apid (annotationRoles inSign)
                             }
        in  concatResult (Result [] (Just (onto, accSign, [])))
                (anaDirective ga accSign onto rest)
    Ax (OntologyProperty _ _ ) ->
                (anaDirective ga inSign onto rest)
    Ax dep@(DEquivalentProperties pid1 pid2 pids) ->
      let Result diags1 maybeRes = checkDRole (pid1:pid2:pids) inSign
      in  case maybeRes of
          Just _ ->
              let namedSent = makeNamed (printQN pid1
                                    ++ "_DataValuedEquivalentProperties_"
                                    ++ printQN pid2)
                              $ OWLAxiom dep
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
              let namedSent = makeNamed (printQN pid1
                                    ++ "_DataValuedSubPropertyOf_"
                                    ++ printQN pid2)
                              $ OWLAxiom dsp
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
              let namedSent = makeNamed (printQN pid1
                                 ++ "_IndividualValuedEquivalentProperties_"
                                 ++ printQN pid2)
                              $ OWLAxiom iep
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
              let namedSent = makeNamed (printQN pid1
                                     ++ "_IndividualValuedSubPropertyOf_"
                                     ++ printQN pid2)
                              $ OWLAxiom isp
              in  concatResult (Result []
                                (Just (Ontology mID (direc ++ [directiv]) ns,
                                       inSign, [namedSent])))
                      (anaDirective ga inSign onto rest)
          _ -> concatResult (Result diags1 Prelude.Nothing)
                   (anaDirective ga inSign onto rest)
    Fc ind@(Indiv (Individual maybeIID _ types values)) ->
       case maybeIID of
        Prelude.Nothing ->          -- Error (Warnung): Individual without name
            -- ignore all anonymous individuals
            anaDirective ga inSign onto rest
        Just iid ->
         if localPart iid == "_" then
    -- if a individual named "_" is it also anonymous individual -> ignored
           anaDirective ga inSign onto rest
           else
            let oriInd = individuals inSign
            in  let (diagL, membershipSet) = msSet iid types ([], Set.empty)
                    ax = axioms inSign
                    accSign =
                        inSign {individuals = Set.insert iid oriInd,
                                axioms = Set.union membershipSet ax
                               }
                    namedSent = if not $ null values then
                                   [ mkDefSen ("Individual_" ++ printQN iid)
                                    $ OWLFact ind ]
                                  else []
                in  concatResult
                         (Result diagL
                          (Just (Ontology mID (direc ++ [directiv]) ns,
                                 accSign, namedSent)))
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

    Fc si@(SameIndividual iid1 iid2 iids) ->
        let namedSent = mkDefSen (printQN iid1
                                      ++ "_SameIndividual_"
                                      ++ (if null iids then printQN iid2
                                             else ""))
                                   $ OWLFact si
        in  concatResult (Result [] (Just (Ontology mID (direc++[directiv]) ns,
                                           inSign, [namedSent])))
                (anaDirective ga inSign onto rest)
    Fc di@(DifferentIndividuals iid1 iid2 iids) ->
        let namedSent = mkDefSen (printQN iid1
                                     ++ "_DifferentIndividuals_"
                                     ++ (if null iids then printQN iid2
                                            else ""))
                                  $ OWLFact di
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

          -- all check-functions check whether the concepts or roles of axioms
          -- already occurred in Sign
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
          -- name of sentences need only the class id.
          printDescForSentName :: Description -> String
          printDescForSentName (DC cid) = printQN cid
          printDescForSentName _ = ""

          -- the intersenctionOf-axiom can be builded from class definition.
          sentOfClass :: ClassID -> [Description] -> [Named Sentence]
          sentOfClass cId descs = case descs of
            _ : _ : _ -> [ mkDefSen (printQN cId ++ "_intersectionOf_")
                         $ OWLAxiom (EquivalentClasses (DC cId)
                                     [IntersectionOf descs]) ]
            _ -> []

nullID :: ID
nullID = QN "" "" ""

initResult :: Result a
initResult = Result [] Prelude.Nothing
