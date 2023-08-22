{- |
Module      :  ./OWL2/StaticAnalysis.hs
Copyright   :  Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Static analysis for OWL 2
-}

module OWL2.StaticAnalysis where

import OWL2.Sign
import OWL2.Morphism
import qualified OWL2.AS as AS
import OWL2.MS
import OWL2.Print ()
import OWL2.Theorem
import OWL2.Function
import OWL2.Symbols

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List

import Common.AS_Annotation hiding (Annotation)
import Common.DocUtils
import Common.Result
import Common.GlobalAnnotations as GA
import Common.ExtSign
import Common.Lib.State
import Common.IRI --(iriToStringUnsecure, setAngles)
import Common.SetColimit

import Control.Monad
import qualified Control.Monad.Fail as Fail

import Logic.Logic

-- | Error messages for static analysis
failMsg :: AS.Entity -> AS.ClassExpression -> Result a
failMsg (AS.Entity _ ty e) desc =
  fatal_error
    ("undeclared `" ++ AS.showEntityType ty
          ++ " " ++ showIRI e ++ "` in the following ClassExpression:\n"
          ++ showDoc desc "") $ iriPos e

-- | checks if an entity is in the signature
checkEntity :: Sign -> AS.Entity -> Result ()
checkEntity s t@(AS.Entity _ ty e) =
  let errMsg = mkError ("unknown " ++ AS.showEntityType ty) e
  in case ty of
   AS.Datatype -> unless (Set.member e (datatypes s) || AS.isDatatypeKey e) errMsg
   AS.Class -> unless (Set.member e (concepts s) || AS.isThing e) errMsg
   AS.ObjectProperty -> unless (isDeclObjProp s $ AS.ObjectProp e) errMsg
   AS.DataProperty -> unless (isDeclDataProp s e) errMsg
   AS.AnnotationProperty -> unless (Set.member e (annotationRoles s)
        || AS.isPredefAnnoProp e) $ justWarn () $ showDoc t " unknown"
   _ -> return ()

-- | takes an iri and finds out what entities it belongs to
correctEntity :: Sign -> IRI -> [AS.Entity]
correctEntity s iri =
    [AS.mkEntity AS.AnnotationProperty iri | Set.member iri (annotationRoles s)] ++
    [AS.mkEntity AS.Class iri | Set.member iri (concepts s)] ++
    [AS.mkEntity AS.ObjectProperty iri | Set.member iri (objectProperties s)] ++
    [AS.mkEntity AS.DataProperty iri | Set.member iri (dataProperties s)] ++
    [AS.mkEntity AS.Datatype iri | Set.member iri (datatypes s)] ++
    [AS.mkEntity AS.NamedIndividual iri | Set.member iri (individuals s)]

checkLiteral :: Sign -> AS.Literal -> Result ()
checkLiteral s l = case l of
    AS.Literal _ (AS.Typed dt) -> checkEntity s $ AS.mkEntity AS.Datatype dt
    _ -> return ()

isDeclInd :: Sign -> AS.Individual -> Bool
isDeclInd s ind = Set.member ind $ individuals s

isDeclObjProp :: Sign -> AS.ObjectPropertyExpression -> Bool
isDeclObjProp s ope = let op = AS.objPropToIRI ope in
    Set.member op (objectProperties s) || AS.isPredefObjProp op

isDeclDataProp :: Sign -> AS.DataPropertyExpression -> Bool
isDeclDataProp s dp = Set.member dp (dataProperties s) || AS.isPredefDataProp dp

{- | takes a list of object properties and discards the ones
    which are not in the signature -}
filterObjProp :: Sign -> [AS.ObjectPropertyExpression]
    -> [AS.ObjectPropertyExpression]
filterObjProp = filter . isDeclObjProp

checkHasKey :: Sign -> [AS.ObjectPropertyExpression] -> [AS.DataPropertyExpression]
    -> Result ([AS.ObjectPropertyExpression], [AS.DataPropertyExpression])
checkHasKey s ol dl = do
    let (declaredObjProps, undeclaredObjs) = partition (isDeclObjProp s) ol
    let (declaredDProps, undeclaredDProps) = partition (isDeclDataProp s) dl

    let newDProps = map (AS.objPropToIRI) $ filter AS.isObjectProperty undeclaredObjs
    let newObjProps = map (AS.ObjectProp) undeclaredDProps

    checkObjPropList s newObjProps
    checkDataPropList s newDProps

    return (declaredObjProps ++ newObjProps, declaredDProps ++ newDProps)

    

checkObjPropList :: Sign -> [AS.ObjectPropertyExpression] -> Result ()
checkObjPropList s ol = do
    let ls = map (isDeclObjProp s) ol
    unless (and ls) $ Fail.fail $ "undeclared object properties:\n" ++
                      showDoc (map (\o -> case o of
                                     AS.ObjectProp _ -> o
                                     AS.ObjectInverseOf x -> x) (filter (not . isDeclObjProp s) ol)) ""

checkDataPropList :: Sign -> [AS.DataPropertyExpression] -> Result ()
checkDataPropList s dl = do
    let ls = map (isDeclDataProp s) dl
    unless (and ls) $ Fail.fail $ "undeclared data properties:\n" ++ showDoc (filter (not . isDeclDataProp s) dl) ""

-- | checks if a DataRange is valid
checkDataRange :: Sign -> AS.DataRange -> Result ()
checkDataRange s dr = case dr of
    AS.DataType dt rl -> do
        checkEntity s $ AS.mkEntity AS.Datatype dt
        mapM_ (checkLiteral s . snd) rl
    AS.DataJunction _ drl -> mapM_ (checkDataRange s) drl
    AS.DataComplementOf r -> checkDataRange s r
    AS.DataOneOf ll -> mapM_ (checkLiteral s) ll

{- | converts ClassExpression to DataRanges because some
     DataProperties may be parsed as ObjectProperties -}
classExpressionToDataRange :: Sign -> AS.ClassExpression -> Result AS.DataRange
classExpressionToDataRange s ce = case ce of
    AS.Expression u -> checkEntity s (AS.mkEntity AS.Datatype u)
        >> return (AS.DataType u [])
    AS.ObjectJunction jt cel -> fmap (AS.DataJunction jt)
        $ mapM (classExpressionToDataRange s) cel
    AS.ObjectComplementOf c -> fmap AS.DataComplementOf
        $ classExpressionToDataRange s c
    _ -> Fail.fail $ "cannot convert ClassExpression to DataRange\n"
            ++ showDoc ce ""

{- | checks a ClassExpression and recursively converts the
     (maybe inappropriately) parsed syntax to a one satisfying the signature -}
checkClassExpression :: Sign -> AS.ClassExpression -> Result AS.ClassExpression
checkClassExpression s desc =
    let errMsg i = failMsg i desc
        objErr i = errMsg $ AS.mkEntity AS.ObjectProperty i
        datErr i = errMsg $ AS.mkEntity AS.DataProperty i
    in case desc of
    AS.Expression u -> if AS.isThing u
        then return $ AS.Expression $ AS.setReservedPrefix u
        else checkEntity s (AS.mkEntity AS.Class u) >> return desc
    AS.ObjectJunction ty ds -> fmap (AS.ObjectJunction ty)
        $ mapM (checkClassExpression s) ds
    AS.ObjectComplementOf d -> fmap AS.ObjectComplementOf $ checkClassExpression s d
    AS.ObjectOneOf _ -> return desc
    AS.ObjectValuesFrom q opExpr d -> if isDeclObjProp s opExpr
        then fmap (AS.ObjectValuesFrom q opExpr) $ checkClassExpression s d
        else let iri = AS.objPropToIRI opExpr
             in if isDeclDataProp s iri then
                    fmap (AS.DataValuesFrom q [iri])
                      $ classExpressionToDataRange s d
                else objErr iri
    AS.ObjectHasSelf opExpr -> if isDeclObjProp s opExpr then return desc
        else objErr $ AS.objPropToIRI opExpr
    AS.ObjectHasValue opExpr _ -> if isDeclObjProp s opExpr then return desc
        else objErr $ AS.objPropToIRI opExpr
    AS.ObjectCardinality (AS.Cardinality a b opExpr md) -> do
        let iri = AS.objPropToIRI opExpr
            mbrOP = Set.member iri $ objectProperties s
        case md of
            Nothing
                | mbrOP -> return desc
                | isDeclDataProp s iri ->
                        return $ AS.DataCardinality $ AS.Cardinality a b iri Nothing
                | otherwise -> objErr iri
            Just d ->
                if mbrOP then fmap (AS.ObjectCardinality . AS.Cardinality a b opExpr
                            . Just) $ checkClassExpression s d
                else do
                    dr <- classExpressionToDataRange s d
                    if isDeclDataProp s iri then
                        return $ AS.DataCardinality
                          $ AS.Cardinality a b iri $ Just dr
                        else datErr iri
    AS.DataValuesFrom _ dExps r -> checkDataRange s r
        >> if all (isDeclDataProp s) dExps then return desc else datErr (head $ filter (not.isDeclDataProp s) dExps)
    AS.DataHasValue dExp l -> do
        checkLiteral s l
        if isDeclDataProp s dExp then return desc
            else datErr dExp
    AS.DataCardinality (AS.Cardinality _ _ dExp mr) -> if isDeclDataProp s dExp
        then case mr of
            Nothing -> return desc
            Just d -> checkDataRange s d >> return desc
        else datErr dExp


checkAnnotation :: Sign -> AS.Annotation -> Result ()
checkAnnotation s (AS.Annotation ans apr av) = do
    checkAnnos s ans
    checkEntity s (AS.mkEntity AS.AnnotationProperty apr)
    case av of
        AS.AnnValLit lit -> checkLiteral s lit
        _ -> return ()

checkAnnos :: Sign -> [AS.Annotation] -> Result ()
checkAnnos = mapM_ . checkAnnotation

checkAssertion :: Sign -> IRI -> Annotations -> Result [Axiom]
checkAssertion s iri ans = do
    let entList = correctEntity s iri
        ab = AnnFrameBit ans $ AnnotationFrameBit Assertion
    if null entList
        then let misc = Misc [AS.Annotation [] iri $ AS.AnnValue iri]
             in return [PlainAxiom misc ab] -- only for anonymous individuals
        else return $ map (\ x -> PlainAxiom (SimpleEntity x) ab) entList

extractDGVariables :: [AS.DGAtom] -> [AS.Variable]
extractDGVariables = 
    let eIArg a = case a of
            AS.IVar v -> [v]
            _ -> []
    in
    
    concat . map (\atom -> case atom of
        AS.DGClassAtom _ a -> eIArg a
        AS.DGObjectPropertyAtom _ a1 a2 -> eIArg a1 ++ eIArg a2
    )

extractVariables :: [AS.Atom] -> [AS.Variable]
extractVariables = 
    let eIArg a = case a of
            AS.IVar v -> [v]
            _ -> []
        eDArg a = case a of
            AS.DVar v -> [v]
            _ -> []
        eUArg a = case a of
            AS.IndividualArg ia -> eIArg ia
            AS.DataArg da -> eDArg da
            AS.Variable v -> [v]
    in
    
    concat . map (\atom -> case atom of
        AS.ClassAtom _ a -> eIArg a
        AS.DataRangeAtom _ a -> eDArg a
        AS.ObjectPropertyAtom _ a1 a2 -> eIArg a1 ++ eIArg a2
        AS.DataPropertyAtom _ a1 a2 -> eIArg a1 ++ eDArg a2
        AS.BuiltInAtom _ args -> concat $ eDArg <$> args
        AS.SameIndividualAtom a1 a2 -> eIArg a1 ++ eIArg a2
        AS.DifferentIndividualsAtom a1 a2 -> eIArg a1 ++ eIArg a2
        AS.UnknownUnaryAtom _ a -> eUArg a
        AS.UnknownBinaryAtom _ a1 a2 -> eUArg a1 ++ eUArg a2
    )

checkIndividualArg :: Sign -> Maybe [AS.Variable] -> AS.IndividualArg -> Result ()
checkIndividualArg s mVars a = case a of
    AS.IArg i -> checkEntity s (AS.mkEntity AS.NamedIndividual i) >> return ()
    AS.IVar v -> case mVars of
        Nothing -> return ()
        Just vars -> unless (v `elem` vars) $ mkError "Unknown variable" v

checkDataArg :: Sign -> Maybe [AS.Variable] -> AS.DataArg -> Result ()
checkDataArg s mVars a = case a of
    AS.DArg l -> checkLiteral s l >> return ()
    AS.DVar v -> case mVars of
        Nothing -> return ()
        Just vars -> unless (v `elem` vars) $ mkError "Unknown variable" v

checkDGAtom :: Sign -> Maybe [AS.Variable] -> AS.DGAtom -> Result AS.DGAtom
checkDGAtom s mVars atom = case atom of
    AS.DGClassAtom c a -> do
        nExpr <- checkClassExpression s c
        checkIndividualArg s mVars a
        return $ AS.DGClassAtom nExpr a
    AS.DGObjectPropertyAtom o a1 a2 -> do
        checkObjPropList s [o]
        checkIndividualArg s mVars a1
        checkIndividualArg s mVars a2
        return atom


checkDLAtom :: Sign -> Maybe [AS.Variable] -> AS.Atom -> Result AS.Atom
checkDLAtom s mVars atom = case atom of
    AS.ClassAtom e a -> do
        newExpr <- checkClassExpression s e
        checkIndividualArg s mVars a
        return $ AS.ClassAtom newExpr a
    AS.DataRangeAtom r a -> do
        checkDataRange s r
        checkDataArg s mVars a
        return atom
    AS.ObjectPropertyAtom o a1 a2 -> do
        checkObjPropList s [o]
        checkIndividualArg s mVars a1
        checkIndividualArg s mVars a2
        return atom
    AS.DataPropertyAtom d a1 a2 -> do
        checkDataPropList s [d]
        checkIndividualArg s mVars a1
        checkDataArg s mVars a2
        return atom
    AS.BuiltInAtom _ args -> do
        mapM (checkDataArg s mVars) args
        return atom
    AS.SameIndividualAtom a1 a2 -> do
        checkIndividualArg s mVars a1
        checkIndividualArg s mVars a2
        return atom
    AS.DifferentIndividualsAtom a1 a2 -> do
        checkIndividualArg s mVars a1
        checkIndividualArg s mVars a2
        return atom
    AS.UnknownUnaryAtom i a -> case a of
        AS.Variable v -> if Set.member i (concepts s)
            then return $ AS.ClassAtom (AS.Expression i) (AS.IVar v)
            else return $ AS.BuiltInAtom i [AS.DVar v]
        _ -> mkError "Unknown unary atom" i
    AS.UnknownBinaryAtom i a1 a2 -> case a1 of
        AS.Variable v ->
            if Set.member i (objectProperties s) then case a2 of
                AS.Variable v2 -> return $ AS.ObjectPropertyAtom (AS.ObjectProp i) (AS.IVar v) (AS.IVar v2)
                AS.IndividualArg a -> return $ AS.ObjectPropertyAtom (AS.ObjectProp i) (AS.IVar v) a
                _ -> mkError "Unknown binary atom" i
            else if Set.member i (dataProperties s) then case a2 of
                AS.Variable v2 -> return $ AS.DataPropertyAtom i (AS.IVar v) (AS.DVar v2)
                AS.DataArg a -> return $ AS.DataPropertyAtom i (AS.IVar v) a
                _ -> mkError "Unknown binary atom" i
            else case a2 of
                AS.Variable v' -> return $ AS.BuiltInAtom i [AS.DVar v']
                AS.DataArg a -> return $ AS.BuiltInAtom i [a]
                _ -> mkError "Unknown binary atom" i 
        AS.IndividualArg a@(AS.IArg _) -> case a2 of
            AS.Variable v ->
                if Set.member i (objectProperties s) then return $ AS.ObjectPropertyAtom (AS.ObjectProp i) a (AS.IVar v)
                else if Set.member i (dataProperties s) then return $ AS.DataPropertyAtom i a (AS.DVar v)
                else mkError "Unknown binary atom" i
            _ -> mkError "Unknown binary atom" i
        _ -> mkError "Unknown binary atom" i


checkDGEdgeAssertion :: Sign -> AS.DGEdgeAssertion -> Result ()
checkDGEdgeAssertion s (AS.DGEdgeAssertion o _ _) = do
    checkObjPropList s [AS.ObjectProp o]
    return ()

-- | corrects the axiom according to the signature
checkAxiom :: Sign -> AS.Axiom -> Result [AS.Axiom]
checkAxiom s a = case a of
    (AS.Declaration anns entity) -> do
        checkAnnos s anns
        checkEntity s entity
        return [a]

    AS.ClassAxiom clAxiom -> case clAxiom of
        AS.SubClassOf anns subClExpr supClExpr -> do
            checkAnnos s anns
            nSubClExpr <- (checkClassExpression s) subClExpr
            nSupClExpr <- (checkClassExpression s) supClExpr
            return [AS.ClassAxiom $ AS.SubClassOf anns nSubClExpr nSupClExpr]

        AS.EquivalentClasses anns clExprs -> do
            checkAnnos s anns
            nClExprs <- mapM (checkClassExpression s) clExprs
            return [AS.ClassAxiom $ AS.EquivalentClasses anns nClExprs]
            
        AS.DisjointClasses anns clExprs -> do
            checkAnnos s anns
            nClExprs <- mapM (checkClassExpression s) clExprs
            return [AS.ClassAxiom $ AS.DisjointClasses anns nClExprs]

        AS.DisjointUnion anns clIRI clExprs -> do
            checkAnnos s anns
            checkEntity s (AS.mkEntity AS.Class clIRI)
            nClExprs <- mapM (checkClassExpression s) clExprs
            return [AS.ClassAxiom $ AS.DisjointUnion anns clIRI nClExprs]

    AS.ObjectPropertyAxiom opAxiom -> case opAxiom of
        AS.SubObjectPropertyOf anns subOpExpr supOpExpr -> do
            let subOpExpr2 = case subOpExpr of
                    AS.SubObjPropExpr_obj o -> [o]
                    AS.SubObjPropExpr_exprchain c -> c
            checkAnnos s anns
            checkObjPropList s (supOpExpr : subOpExpr2)
            return [a]

        AS.EquivalentObjectProperties anns opExprs -> do
            checkAnnos s anns
            checkObjPropList s opExprs
            return [a]

        AS.DisjointObjectProperties anns opExprs -> do
            checkAnnos s anns
            checkObjPropList s opExprs
            return [a]

        AS.InverseObjectProperties anns opExpr1 opExpr2 -> do
            checkAnnos s anns
            checkObjPropList s [opExpr1, opExpr2]
            return [a]

        AS.ObjectPropertyDomain anns opExpr clExpr -> do
            checkAnnos s anns
            checkObjPropList s [opExpr]
            nClExpr <- checkClassExpression s clExpr
            return [AS.ObjectPropertyAxiom
                $ AS.ObjectPropertyDomain anns opExpr nClExpr]

        AS.ObjectPropertyRange anns opExpr clExpr -> do
            checkAnnos s anns
            checkObjPropList s [opExpr]
            nClExpr <- checkClassExpression s clExpr
            return [AS.ObjectPropertyAxiom
                $ AS.ObjectPropertyRange anns opExpr nClExpr]

        AS.FunctionalObjectProperty anns opExpr -> do
            checkAnnos s anns
            checkObjPropList s [opExpr]
            return [a]

        AS.InverseFunctionalObjectProperty anns opExpr -> do
            checkAnnos s anns
            checkObjPropList s [opExpr]
            return [a]

        AS.ReflexiveObjectProperty anns opExpr -> do
            checkAnnos s anns
            checkObjPropList s [opExpr]
            return [a]

        AS.IrreflexiveObjectProperty anns opExpr -> do
            checkAnnos s anns
            checkObjPropList s [opExpr]
            return [a]

        AS.SymmetricObjectProperty anns opExpr -> do
            checkAnnos s anns
            checkObjPropList s [opExpr]
            return [a]

        AS.AsymmetricObjectProperty anns opExpr -> do
            checkAnnos s anns
            checkObjPropList s [opExpr]
            return [a]

        AS.TransitiveObjectProperty anns opExpr -> do
            checkAnnos s anns
            checkObjPropList s [opExpr]
            return [a]

    (AS.DataPropertyAxiom dpAxiom) -> case dpAxiom of
        AS.SubDataPropertyOf anns subDpExpr supDpExpr -> do
            checkAnnos s anns
            checkDataPropList s [subDpExpr, supDpExpr]
            return [a]

        AS.EquivalentDataProperties anns dpExprs -> do
            checkAnnos s anns
            unless (length dpExprs >= 2) $ mkError "Incorrect number of Data Property Expressions (must be >= 2): " dpExprs
            checkDataPropList s dpExprs
            return [a]

        AS.DisjointDataProperties anns dpExprs -> do
            checkAnnos s anns
            unless (length dpExprs >= 2) $ mkError "Incorrect number of Data Property Expressions (must be >= 2): " dpExprs
            checkDataPropList s dpExprs
            return [a]

        AS.DataPropertyDomain anns dpExpr clExpr -> do
            checkAnnos s anns
            checkDataPropList s [dpExpr]
            nClExpr <- checkClassExpression s clExpr
            return [AS.DataPropertyAxiom
                $ AS.DataPropertyDomain anns dpExpr nClExpr]

        AS.DataPropertyRange anns dpExpr dr -> do
            checkAnnos s anns
            checkDataPropList s [dpExpr]
            checkDataRange s dr
            return [a]

        AS.FunctionalDataProperty anns dpExpr -> do
            checkAnnos s anns
            checkDataPropList s [dpExpr]
            return [a]
            
    AS.DatatypeDefinition anns dt dr -> do
        checkAnnos s anns
        checkEntity s $ AS.mkEntity AS.Datatype dt
        checkDataRange s dr
        return [a]

    AS.HasKey anns clExpr opExprs dpExprs -> do
        checkAnnos s anns
        nClExpr <- checkClassExpression s clExpr
        (nOpExprs, nDpExprs) <- checkHasKey s opExprs dpExprs
        return [AS.HasKey anns nClExpr nOpExprs nDpExprs]

    AS.Assertion assertionAxiom -> case assertionAxiom of 
        AS.SameIndividual anns inds -> do
            checkAnnos s anns
            unless (length inds >= 2) $ mkError "Incorrect number of Individuals (must be >= 2): " inds
            mapM_ (checkEntity s . AS.mkEntity AS.NamedIndividual) inds 
            return [a]
            
        AS.DifferentIndividuals anns inds -> do
            checkAnnos s anns
            unless (length inds >= 2) $ mkError "Incorrect number of Individuals (must be >= 2): " inds
            mapM_ (checkEntity s . AS.mkEntity AS.NamedIndividual) inds
            return [a]

        AS.ClassAssertion anns clExpr ind -> do
            checkAnnos s anns
            nClExpr <- checkClassExpression s clExpr
            checkEntity s $ AS.mkEntity AS.NamedIndividual ind
            return [AS.Assertion $ AS.ClassAssertion anns nClExpr ind]

        AS.ObjectPropertyAssertion anns opExpr sInd tInd -> do
            checkAnnos s anns
            checkObjPropList s [opExpr]
            mapM_ (checkEntity s . AS.mkEntity AS.NamedIndividual) [sInd, tInd]
            return [a]

        AS.NegativeObjectPropertyAssertion anns opExpr sInd tInd -> do
            checkAnnos s anns
            checkObjPropList s [opExpr]
            mapM_ (checkEntity s . AS.mkEntity AS.NamedIndividual) [sInd, tInd]
            return [a]

        AS.DataPropertyAssertion anns dpExpr sInd tValue -> do
            checkAnnos s anns
            checkDataPropList s [dpExpr]
            checkEntity s $ AS.mkEntity AS.NamedIndividual sInd
            checkLiteral s tValue
            return [a]

        AS.NegativeDataPropertyAssertion anns dpExpr sInd tValue -> do
            checkAnnos s anns
            checkDataPropList s [dpExpr]
            checkEntity s $ AS.mkEntity AS.NamedIndividual sInd
            checkLiteral s tValue
            return [a]

    AS.AnnotationAxiom anAxiom -> case anAxiom of
        AS.AnnotationAssertion anns prop subj val -> do
            checkAnnos s anns
            checkEntity s (AS.mkEntity AS.AnnotationProperty prop)

            case subj of
                AS.AnnSubIri iri -> when (null $ correctEntity s iri)
                    $ mkError "Incorrect AnnotationAssertion axiom. Axiom subject is not declared: " (show iri)
                _ -> return ()
                
            case val of
                AS.AnnValLit lit -> checkLiteral s lit
                _ -> return ()
            return [a]
            

        AS.SubAnnotationPropertyOf anns subAnProp supAnProp -> do
            checkAnnos s anns
            mapM_ (checkEntity s . AS.mkEntity AS.AnnotationProperty) [subAnProp, supAnProp]
            return [a]

        AS.AnnotationPropertyDomain anns prop _ -> do
            checkAnnos s anns
            checkEntity s (AS.mkEntity AS.AnnotationProperty prop)
            return [a]

        AS.AnnotationPropertyRange anns prop _ -> do
            checkAnnos s anns
            checkEntity s (AS.mkEntity AS.AnnotationProperty prop)
            return [a]
        

    (AS.Rule rule) -> case rule of 
        AS.DLSafeRule anns body hea -> do
            checkAnnos s anns
            nBody <- mapM (checkDLAtom s Nothing) body
            let vars = extractVariables body
            nHead <- mapM (checkDLAtom s (Just vars)) hea
            return [AS.Rule $ AS.DLSafeRule anns nBody nHead]
        AS.DGRule anns body hea -> do
            checkAnnos s anns
            mapM (checkDGAtom s Nothing) body
            let vars = extractDGVariables body
            mapM (checkDGAtom s (Just vars)) hea
            return [a]
    (AS.DGAxiom anns _ _ edges _) -> do
        checkAnnos s anns
        mapM (checkDGEdgeAssertion s) edges
        return [a]



correctFrames :: Sign -> [AS.Axiom] -> Result [AS.Axiom]
correctFrames s = fmap concat . mapM (checkAxiom s)

collectEntities :: AS.Axiom -> State Sign ()
collectEntities f = case f of
    AS.Declaration _ e -> addEntity e
    _ -> return ()

-- | collects all entites from the aximoms
createSign :: [AS.Axiom] -> State Sign ()
createSign f = do
  pm <- gets prefixMap
  mapM_ (collectEntities . function Expand (StringMap pm)) f

noDecl :: AS.Axiom -> Bool
noDecl ax = case ax of
  AS.Declaration _ _ -> False
  _ -> True

-- | corrects the axioms according to the signature
createAxioms :: Sign -> [AS.Axiom] -> Result ([Named AS.Axiom], [AS.Axiom])
createAxioms s fl = do
    cf <- correctFrames s $ map (function Expand $ StringMap $ prefixMap s) fl
    return (map anaAxiom . filter noDecl $ cf, cf)

check1Prefix :: Maybe IRI -> IRI -> Bool
check1Prefix ms s = case ms of
      Nothing -> True
      Just iri -> iri == s

checkPrefixMap :: GA.PrefixMap -> Bool
checkPrefixMap pm =
    let pl = map (`Map.lookup` pm) ["owl", "rdf", "rdfs", "xsd"]
    in and $ zipWith check1Prefix pl
            (map snd $ Map.toList AS.predefPrefixesGA)

newODoc :: AS.OntologyDocument -> [AS.Axiom] -> Result AS.OntologyDocument
newODoc AS.OntologyDocument {
      AS.ontology = mo
    , AS.ontologyMetadata = md
    , AS.prefixDeclaration = pd} ax =
    if checkPrefixMap pd
        then return AS.OntologyDocument
                { AS.ontologyMetadata = md
                , AS.ontology = mo {AS.axioms = ax}
                , AS.prefixDeclaration = pd
                }
        else Fail.fail $ "Incorrect predefined prefixes " ++ showDoc pd "\n"

-- | static analysis of ontology with incoming sign.
basicOWL2Analysis :: (AS.OntologyDocument, Sign, GlobalAnnos)
    -> Result (AS.OntologyDocument, ExtSign Sign AS.Entity, [Named AS.Axiom])
basicOWL2Analysis (inOnt, inSign, ga) = do
    let pm = Map.union (AS.prefixDeclaration inOnt)
          . Map.delete "" $ prefix_map ga
        odoc = inOnt { AS.prefixDeclaration = pm }
        axs = AS.axioms $ AS.ontology odoc
        accSign = execState (createSign axs) inSign { prefixMap = AS.changePrefixMapTypeToString pm }
        syms = Set.difference (symOf accSign) $ symOf inSign
    (axl, nfl) <- createAxioms accSign axs
    newdoc <- newODoc odoc nfl
    return (newdoc
      , ExtSign accSign {labelMap = generateLabelMap accSign nfl} syms, axl)

-- | extract labels from Axiom-List (after processing with correctFrames)
generateLabelMap :: Sign -> [AS.Axiom] -> Map.Map IRI String
generateLabelMap sig = foldr (\ a -> case a of 
        AS.AnnotationAxiom ax -> case ax of
            AS.AnnotationAssertion _ apr sub (AS.AnnValLit (AS.Literal s' _))
                | prefixName apr == "rdfs" && show (iriPath apr) == "label"
                -> Map.insert (ir sub) s'
            _ -> id
        _ -> id) (labelMap sig)
    where ir sub = case sub of
            AS.AnnSubIri i -> i
            AS.AnnSubAnInd i -> i 

-- | adding annotations for theorems
anaAxiom :: AS.Axiom -> Named AS.Axiom
anaAxiom ax = findImplied ax $ makeNamed nm ax
   where names = getNames ax
         nm = concat $ intersperse "_" names
         
findImplied :: AS.Axiom -> Named AS.Axiom -> Named AS.Axiom
findImplied ax sent =
  if prove ax then sent
         { isAxiom = False
         , isDef = False
         , wasTheorem = False }
   else sent { isAxiom = True }

getNamesFromAnnos :: [AS.Annotation] -> [String]
getNamesFromAnnos = concat . fmap (\anno -> case anno of
      AS.Annotation _ aIRI (AS.AnnValLit (AS.Literal value _)) ->
          if show (iriPath aIRI) == "label"
             then [value]
             else []
      _ -> [])

getNames :: AS.Axiom -> [String]
getNames ax = case ax of
    AS.Declaration anns _ -> getNamesFromAnnos anns
    AS.ClassAxiom cax -> case cax of
        AS.SubClassOf anns _ _ -> getNamesFromAnnos anns
        AS.EquivalentClasses anns _ -> getNamesFromAnnos anns
        AS.DisjointClasses anns _ -> getNamesFromAnnos anns
        AS.DisjointUnion anns _ _ -> getNamesFromAnnos anns
    AS.ObjectPropertyAxiom opax -> case opax of
        AS.SubObjectPropertyOf anns _ _ -> getNamesFromAnnos anns
        AS.EquivalentObjectProperties anns _ -> getNamesFromAnnos anns
        AS.DisjointObjectProperties anns _ -> getNamesFromAnnos anns
        AS.InverseObjectProperties anns _ _ -> getNamesFromAnnos anns
        AS.ObjectPropertyDomain anns _ _ -> getNamesFromAnnos anns
        AS.ObjectPropertyRange anns _ _ -> getNamesFromAnnos anns
        AS.FunctionalObjectProperty anns _ -> getNamesFromAnnos anns
        AS.InverseFunctionalObjectProperty anns _ -> getNamesFromAnnos anns
        AS.ReflexiveObjectProperty anns _ -> getNamesFromAnnos anns
        AS.IrreflexiveObjectProperty anns _ -> getNamesFromAnnos anns
        AS.SymmetricObjectProperty anns _ -> getNamesFromAnnos anns
        AS.AsymmetricObjectProperty anns _ -> getNamesFromAnnos anns
        AS.TransitiveObjectProperty anns _ -> getNamesFromAnnos anns
    AS.DataPropertyAxiom a -> case a of
        AS.SubDataPropertyOf anns _ _ -> getNamesFromAnnos anns
        AS.EquivalentDataProperties anns _ -> getNamesFromAnnos anns
        AS.DisjointDataProperties anns _ -> getNamesFromAnnos anns
        AS.DataPropertyDomain anns _ _ -> getNamesFromAnnos anns
        AS.DataPropertyRange anns _ _ -> getNamesFromAnnos anns
        AS.FunctionalDataProperty anns _ -> getNamesFromAnnos anns
    AS.DatatypeDefinition anns _ _ -> getNamesFromAnnos anns
    AS.HasKey anns _ _ _ -> getNamesFromAnnos anns
    AS.Assertion a -> case a of
        AS.SameIndividual anns _ -> getNamesFromAnnos anns
        AS.DifferentIndividuals anns _ -> getNamesFromAnnos anns
        AS.ClassAssertion anns _ _ -> getNamesFromAnnos anns
        AS.ObjectPropertyAssertion anns _ _ _ -> getNamesFromAnnos anns
        AS.NegativeObjectPropertyAssertion anns _ _ _ -> getNamesFromAnnos anns
        AS.DataPropertyAssertion anns _ _ _ -> getNamesFromAnnos anns
        AS.NegativeDataPropertyAssertion anns _ _ _ -> getNamesFromAnnos anns
    AS.AnnotationAxiom a -> case a of
        AS.AnnotationAssertion anns _ _ _ -> getNamesFromAnnos anns
        AS.SubAnnotationPropertyOf anns _ _ -> getNamesFromAnnos anns
        AS.AnnotationPropertyDomain anns _ _ -> getNamesFromAnnos anns
        AS.AnnotationPropertyRange anns _ _ -> getNamesFromAnnos anns
    AS.DGAxiom anns _ _ _ _ -> getNamesFromAnnos anns
    AS.Rule r -> case r of
        AS.DLSafeRule anns _ _ -> getNamesFromAnnos anns
        AS.DGRule anns _ _ -> getNamesFromAnnos anns


addEquiv :: Sign -> Sign -> [SymbItems] -> [SymbItems] ->
            Result (Sign, Sign, Sign,
                     EndoMap AS.Entity, EndoMap AS.Entity)
addEquiv ssig tsig l1 l2 = do
  let l1' = statSymbItems ssig l1
      l2' = statSymbItems tsig l2
  case (l1', l2') of
    ([rs1], [rs2]) -> do
      let match1 = filter (`matchesSym` rs1) $ Set.toList $ symOf ssig
          match2 = filter (`matchesSym` rs2) $ Set.toList $ symOf tsig
      case
       (match1, match2) of
          ([e1], [e2]) ->
           if AS.entityKind e1 == AS.entityKind e2 then do
              s <- AS.pairSymbols e1 e2
              sig <- addSymbToSign emptySign s
              sig1 <- addSymbToSign emptySign e1
              sig2 <- addSymbToSign emptySign e2
              return (sig, sig1, sig2,
                         Map.insert e1 s Map.empty,
                         Map.insert e2 s Map.empty)
             else
              Fail.fail "only symbols of same kind can be equivalent in an alignment"
          _ -> Fail.fail $ "non-unique symbol match:" ++ showDoc l1 " "
                                                 ++  showDoc l2 " "
    _ -> Fail.fail "terms not yet supported in alignments"

corr2theo :: String -> Bool -> Sign -> Sign -> [SymbItems] -> [SymbItems] ->
             EndoMap AS.Entity -> EndoMap AS.Entity -> REL_REF ->
             Result (Sign, [Named AS.Axiom], Sign, Sign,
                     EndoMap AS.Entity, EndoMap AS.Entity)
corr2theo _aname flag ssig tsig l1 l2 eMap1 eMap2 rref = do
  let l1' = statSymbItems ssig l1
      l2' = statSymbItems tsig l2
  case (l1', l2') of
    ([rs1], [rs2]) -> do
      let match1 = filter (`matchesSym` rs1) $ Set.toList $ symOf ssig
          match2 = filter (`matchesSym` rs2) $ Set.toList $ symOf tsig
      case
       (match1, match2) of
          ([e1], [e2]) -> do
           let e1' = if flag then e1 {AS.cutIRI =  addString (AS.cutIRI e1, "_source")} else e1
               e2' = if flag then e2 {AS.cutIRI =  addString (AS.cutIRI e2, "_target")} else e2
               sig = emptySign
               eMap1' = Map.union eMap1 $ Map.fromAscList [(e1', e1)]
               eMap2' = Map.union eMap2 $ Map.fromAscList [(e2', e2)]
           sig1 <- addSymbToSign sig e1'
           sig2 <- addSymbToSign sig e2'
           sigB <- addSymbToSign sig1 e2'
           case rref of
            Equiv -> do
                let axiom = case (AS.entityKind e1', AS.entityKind e2') of
                        (AS.Class, AS.Class) -> AS.ClassAxiom $
                                AS.EquivalentClasses [] (AS.Expression . AS.cutIRI <$> [e1', e2'])
                        (AS.ObjectProperty, AS.ObjectProperty) -> AS.ObjectPropertyAxiom $
                            AS.EquivalentObjectProperties [] (AS.ObjectProp . AS.cutIRI <$> [e1', e2'])
                        (AS.NamedIndividual, AS.NamedIndividual) -> AS.Assertion $
                            AS.SameIndividual [] (AS.cutIRI <$> [e1', e2'])
                        _ -> error $ "use subsumption only between"
                                        ++ "classes or roles:" ++
                                        show l1 ++ " " ++ show l2
                return (sigB, [makeNamed "" axiom], sig1, sig2, eMap1', eMap2')
            Subs -> do
                let axiom = case (AS.entityKind e1', AS.entityKind e2') of
                        (AS.Class, AS.Class) -> AS.ClassAxiom $
                            AS.SubClassOf []
                                (AS.Expression . AS.cutIRI $ e1')
                                (AS.Expression . AS.cutIRI $ e2')
                        (AS.ObjectProperty, AS.ObjectProperty) -> AS.ObjectPropertyAxiom $
                            AS.SubObjectPropertyOf []
                                (AS.SubObjPropExpr_obj $ AS.ObjectProp $ AS.cutIRI e1')
                                (AS.ObjectProp $ AS.cutIRI e2')
                        _ -> error $ "use subsumption only between"
                                        ++ "classes or roles:" ++
                                        show l1 ++ " " ++ show l2
                return (sigB, [makeNamed "" axiom], sig1, sig2, eMap1', eMap2')
            Incomp -> do
                let axiom = AS.ClassAxiom $ AS.DisjointClasses [] (AS.Expression . AS.cutIRI <$> [e1', e2'])
                return (sigB, [makeNamed "" axiom], sig1, sig2, eMap1', eMap2')
            IsSubs -> do
                let axiom = AS.ClassAxiom $ AS.SubClassOf []
                        (AS.Expression . AS.cutIRI $ e1')
                        (AS.Expression . AS.cutIRI $ e2')
                return (sigB, [makeNamed "" axiom], sig1, sig2, eMap1', eMap2')
            InstOf -> do
                let axiom = AS.Assertion $ AS.ClassAssertion []
                        (AS.Expression . AS.cutIRI $ e1')
                        (AS.cutIRI $ e2')
                return
                    (sigB, [makeNamed "" axiom], sig1, sig2, eMap1', eMap2')
            HasInst -> do
                let axiom = AS.Assertion $ AS.ClassAssertion []
                        (AS.Expression . AS.cutIRI $ e2')
                        (AS.cutIRI $ e1')
                return
                    (sigB, [makeNamed "" axiom], sig1, sig2, eMap1', eMap2')
            RelName _r -> error "nyi" {- do
             let extPart = mkExtendedEntity e1'
                 rQName = QN "" (iriToStringUnsecure r)
                             Abbreviated (iriToStringUnsecure r) Id.nullRange
                 sym = mkEntity ObjectProperty rQName
                 rSyms = filter (== sym) $
                            Set.toList $ symOf tsig
             case rSyms of
               [] -> Fail.fail $ "relation " ++ show rQName ++
                                " not in " ++ show tsig
               [rsym] -> do
                 let sym'@(Entity _ ObjectProperty rQName') =
                             Map.findWithDefault rsym rsym eMap2'
                     axiom = PlainAxiom extPart $
                              ListFrameBit (Just SubClass) $
                               ExpressionBit [([],
                                ObjectValuesFrom
                                 SomeValuesFrom
                                 (ObjectProp rQName')
                                 (Expression $ cutIRI e2'))]
                 sigB' <- addSymbToSign sigB sym'
                 sig2' <- addSymbToSign sig2 rsym
                 return
                   (sigB', [makeNamed "" axiom], sig1, sig2', eMap1',
                      Map.union eMap2' $ Map.fromAscList [(rsym, sym')])
               _ -> Fail.fail $ "too many matches for " ++ show rQName -}
            _ -> Fail.fail $ "nyi:" ++ show rref
          _ -> Fail.fail $ "non-unique symbol match:" ++ showDoc l1 " "
                                                 ++ showDoc l2 " "
    _ -> Fail.fail "terms not yet supported in alignments"
