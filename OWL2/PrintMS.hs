module OWL2.PrintMS where

import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Keywords
import Common.IRI

import OWL2.AS
import OWL2.Keywords
import OWL2.ColonKeywords

-- imports for tests
import qualified OWL2.ParseAS as Parser
import Common.Parsec
import Text.ParserCombinators.Parsec (parse)
import Debug.Trace

----- auxiliary data structures and transformations (possible MS syntax) -----

-- | tmp function to extract IRI from ObjectInverseOf
obPropExprToIRI :: ObjectPropertyExpression -> IRI
obPropExprToIRI (ObjectProp iri) = iri
obPropExprToIRI (ObjectInverseOf obExpr) = obPropExprToIRI obExpr 

type Annotations = [Annotation]

data FrameIdValue = 
      IriId IRI
    | ObjInvOfId IRI
    | MiscId
    deriving(Show, Eq, Ord)

type FrameId = (String, FrameIdValue)
type Frame = M.Map String [Axiom]
type MnchstrSntx = M.Map FrameId Frame

emptyMS :: MnchstrSntx
emptyMS = M.empty

tabs :: Int -> Doc
tabs n
    | n < 1 = empty
    | otherwise = text ['\t' | _ <- [1..n]]

-- transfromation functions.
-- From FS to intermediate MS
-- | transform Axioms
tAxioms :: [Axiom] -> MnchstrSntx -> MnchstrSntx
tAxioms = flip $ foldr tAxiom

-- | transform Axiom
tAxiom :: Axiom -> MnchstrSntx -> MnchstrSntx
tAxiom axiom ms = case axiom of
    Declaration {} -> tDeclaration axiom ms
    ClassAxiom ca -> tClassAxiom ca ms
    ObjectPropertyAxiom opa -> tObjectPropertyAxiom opa ms
    DataPropertyAxiom dpa -> tDataPropertyAxiom dpa ms
    HasKey {} -> tHasKey axiom ms

-- | transform Declaration
tDeclaration :: Axiom -> MnchstrSntx -> MnchstrSntx
tDeclaration (Declaration anns entity) = tEntity entity . tDecAnnotations anns

-- | transform Annotations v1
tDecAnnotations :: Annotations -> MnchstrSntx -> MnchstrSntx
tDecAnnotations = flip $ foldr tDecAnnotation

-- | transform Annotation v1
tDecAnnotation :: Annotation -> MnchstrSntx -> MnchstrSntx
tDecAnnotation (Annotation anns annProp _) ms =
    tDecAnnotations anns
        $ M.insert k v ms
    where 
        k = ("AnnotationProperty", IriId annProp)
        v = M.findWithDefault M.empty k ms

-- | transform Entity
tEntity :: Entity -> MnchstrSntx -> MnchstrSntx
tEntity entity ms = case (entityKind entity) of
    Datatype ->
        if M.notMember ("Datatype", IriId iri) ms
            then M.insert ("Datatype", IriId iri) M.empty ms
            else ms

    Class -> 
        if M.notMember ("Class", IriId iri) ms
            then M.insert ("Class", IriId iri) M.empty ms
            else ms

    ObjectProperty ->
        if M.notMember ("ObjectProperty", IriId iri) ms
            then M.insert ("ObjectProperty", IriId iri) M.empty ms
            else ms

    DataProperty -> 
        if M.notMember ("DataProperty", IriId iri) ms
            then M.insert ("DataProperty", IriId iri) M.empty ms
            else ms

    AnnotationProperty ->
        if M.notMember ("AnnotationProperty", IriId iri) ms
            then M.insert ("AnnotationProperty", IriId iri) M.empty ms
            else ms
    
    NamedIndividual ->
        if M.notMember ("Individual", IriId iri) ms
            then M.insert ("Individual", IriId iri) M.empty ms
            else ms

    where iri = cutIRI entity

-- | transform ObjectProperty axiom
tObjectPropertyAxiom :: ObjectPropertyAxiom -> MnchstrSntx -> MnchstrSntx
-- SubObjectPropertyOf axiom
tObjectPropertyAxiom opAx@(SubObjectPropertyOf anns 
    (SubObjPropExpr_obj opExpr1) opExpr2) ms =
    M.insert ("ObjectProperty", fIdValue)
        (M.insert "subPropertyOf" newAxioms m2) m1
    where
        fIdValue = case opExpr1 of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr

        m1 = tAnnotations anns . tObjectPropertyExpression True opExpr1 $ ms
        m2 = M.findWithDefault M.empty ("ObjectProperty", fIdValue) m1
        axioms = M.findWithDefault [] "subPropertyOf" m2
        newAxioms = S.toList . S.fromList $ ObjectPropertyAxiom opAx : axioms

tObjectPropertyAxiom opAx@(SubObjectPropertyOf anns
    (SubObjPropExpr_exprchain opExprs) (ObjectProp iri)) ms =
    M.insert fid (M.insert "subPropertyChain" newAxioms m2) m1
    where
        fid = ("ObjectProperty", IriId iri)
        m1 = tAnnotations anns . tObjectPropertyExpressions False opExprs $ ms
        m2 = M.findWithDefault M.empty fid m1
        axioms = M.findWithDefault [] "subPropertyChain" m2
        newAxioms = S.toList . S.fromList $ ObjectPropertyAxiom opAx : axioms

tObjectPropertyAxiom (SubObjectPropertyOf anns 
    (SubObjPropExpr_obj opExpr1) opExpr2) ms =
    tAnnotations anns . tObjectPropertyExpressions False [opExpr1, opExpr2] $ ms

tObjectPropertyAxiom (SubObjectPropertyOf anns
    (SubObjPropExpr_exprchain opExprs) opExpr) ms =
    tAnnotations anns . tObjectPropertyExpressions False opExprs
    . tObjectPropertyExpression False opExpr $ ms

-- EquivalentObjectProperties axiom
tObjectPropertyAxiom opAx@(EquivalentObjectProperties anns
    [opExpr1, opExpr2]) ms =
    M.insert ("ObjectProperty", fIdValue1)
        (M.insert "equivalentTo" newAxioms1 m1)
    . M.insert ("ObjectProperty", fIdValue2) 
        (M.insert "equivalentTo" newAxioms2 m2) $ m'
    where
        fIdValue1 = case opExpr1 of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr

        fIdValue2 = case opExpr2 of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr

        m' = tAnnotations anns ms
        m1 = M.findWithDefault M.empty ("ObjectProperty", fIdValue1) m'
        m2 = M.findWithDefault M.empty ("ObjectProperty", fIdValue2) m'
        axioms1 = M.findWithDefault [] "equivalentTo" m1
        axioms2 = M.findWithDefault [] "equivalentTo" m2
        newAxioms1 = S.toList . S.fromList $ ObjectPropertyAxiom opAx : axioms1
        newAxioms2 = S.toList . S.fromList
            $ (ObjectPropertyAxiom . EquivalentObjectProperties anns $
                [opExpr2, opExpr1]) : axioms2

tObjectPropertyAxiom opAx@(EquivalentObjectProperties anns opExprs) ms =
    M.insert ("Misc", MiscId)
        (M.insert "equivalentProperties" newAxioms m1) $ m'
    where
        m' = tAnnotations anns . tObjectPropertyExpressions True opExprs $ ms
        m1 = M.findWithDefault M.empty ("Misc", MiscId) m'
        axioms = M.findWithDefault [] "equivalentProperties" m1
        newAxioms = S.toList . S.fromList $ ObjectPropertyAxiom opAx : axioms

-- DisjointObjectProperties axiom
tObjectPropertyAxiom opAx@(DisjointObjectProperties anns
    [opExpr1, opExpr2]) ms =
    M.insert ("ObjectProperty", fIdValue1)
        (M.insert "disjointWith" newAxioms1 m1)
    . M.insert ("ObjectProperty", fIdValue2) 
        (M.insert "disjointWith" newAxioms2 m2) $ m'
    where
        fIdValue1 = case opExpr1 of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr

        fIdValue2 = case opExpr2 of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr

        m' = tAnnotations anns ms
        m1 = M.findWithDefault M.empty ("ObjectProperty", fIdValue1) m'
        m2 = M.findWithDefault M.empty ("ObjectProperty", fIdValue2) m'
        axioms1 = M.findWithDefault [] "disjointWith" m1
        axioms2 = M.findWithDefault [] "disjointWith" m2
        newAxioms1 = S.toList . S.fromList $ ObjectPropertyAxiom opAx : axioms1
        newAxioms2 = S.toList . S.fromList
            $ (ObjectPropertyAxiom . DisjointObjectProperties anns $
                [opExpr2, opExpr1]) : axioms2

tObjectPropertyAxiom opAx@(DisjointObjectProperties anns opExprs) ms =
    M.insert ("Misc", MiscId)
        (M.insert "disjointProperties" newAxioms m1) $ m'
    where
        m' = tAnnotations anns . tObjectPropertyExpressions True opExprs $ ms
        m1 = M.findWithDefault M.empty ("Misc", MiscId) m'
        axioms = M.findWithDefault [] "disjointProperties" m1
        newAxioms = S.toList . S.fromList $ ObjectPropertyAxiom opAx : axioms

-- InverseObjectProperties axiom
tObjectPropertyAxiom opAx@(InverseObjectProperties anns opExpr1 opExpr2) ms =
    M.insert ("ObjectProperty", fIdValue1)
        (M.insert "inverseOf" newAxioms1 m1)
    . M.insert ("ObjectProperty", fIdValue2) 
        (M.insert "inverseOf" newAxioms2 m2) $ m'
    where
        fIdValue1 = case opExpr1 of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr

        fIdValue2 = case opExpr2 of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr

        m' = tAnnotations anns
            . tObjectPropertyExpressions True [opExpr1, opExpr2] $ ms
        m1 = M.findWithDefault M.empty ("ObjectProperty", fIdValue1) m'
        m2 = M.findWithDefault M.empty ("ObjectProperty", fIdValue2) m'
        axioms1 = M.findWithDefault [] "inverseOf" m1
        axioms2 = M.findWithDefault [] "inverseOf" m2
        newAxioms1 = S.toList . S.fromList $ ObjectPropertyAxiom opAx : axioms1
        newAxioms2 = S.toList . S.fromList
            $ (ObjectPropertyAxiom $ InverseObjectProperties anns
                opExpr2 opExpr1) : axioms2

-- ObjectPropertyDomain axiom
tObjectPropertyAxiom opAx@(ObjectPropertyDomain anns opExpr clExpr) ms =
   M.insert ("ObjectProperty", fIdValue) (M.insert "domain" newAxioms m2) m1
   where
        fIdValue = case opExpr of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr
        m1 = tAnnotations anns . tObjectPropertyExpression True opExpr
            . tClassExpression clExpr $ ms
        m2 = M.findWithDefault M.empty ("ObjectProperty", fIdValue) m1
        axioms = M.findWithDefault [] "domain" m2
        newAxioms = S.toList . S.fromList $ ObjectPropertyAxiom opAx : axioms

-- ObjectPropertyRange axiom
tObjectPropertyAxiom opAx@(ObjectPropertyRange anns opExpr clExpr) ms =
   M.insert ("ObjectProperty", fIdValue) (M.insert "range" newAxioms m2) m1
   where
        fIdValue = case opExpr of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr
        m1 = tAnnotations anns . tObjectPropertyExpression True opExpr
            . tClassExpression clExpr $ ms
        m2 = M.findWithDefault M.empty ("ObjectProperty", fIdValue) m1
        axioms = M.findWithDefault [] "range" m2
        newAxioms = S.toList . S.fromList $ ObjectPropertyAxiom opAx : axioms

-- FunctionalObjectProperty axiom
tObjectPropertyAxiom opAx@(FunctionalObjectProperty anns opExpr) ms =
   M.insert ("ObjectProperty", fIdValue) (M.insert "characteristics" newAxioms m2) m1
   where
        fIdValue = case opExpr of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr
        m1 = tAnnotations anns . tObjectPropertyExpression True opExpr $ ms
        m2 = M.findWithDefault M.empty ("ObjectProperty", fIdValue) m1
        axioms = M.findWithDefault [] "characteristics" m2
        newAxioms = S.toList . S.fromList $ ObjectPropertyAxiom opAx : axioms


-- InverseFunctionalObjectProperty axiom
tObjectPropertyAxiom opAx@(InverseFunctionalObjectProperty anns opExpr) ms =
   M.insert ("ObjectProperty", fIdValue) (M.insert "characteristics" newAxioms m2) m1
   where
        fIdValue = case opExpr of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr
        m1 = tAnnotations anns . tObjectPropertyExpression True opExpr $ ms
        m2 = M.findWithDefault M.empty ("ObjectProperty", fIdValue) m1
        axioms = M.findWithDefault [] "characteristics" m2
        newAxioms = S.toList . S.fromList $ ObjectPropertyAxiom opAx : axioms

-- ReflexiveObjectProperty axiom
tObjectPropertyAxiom opAx@(ReflexiveObjectProperty anns opExpr) ms =
   M.insert ("ObjectProperty", fIdValue) (M.insert "characteristics" newAxioms m2) m1
   where
        fIdValue = case opExpr of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr
        m1 = tAnnotations anns . tObjectPropertyExpression True opExpr $ ms
        m2 = M.findWithDefault M.empty ("ObjectProperty", fIdValue) m1
        axioms = M.findWithDefault [] "characteristics" m2
        newAxioms = S.toList . S.fromList $ ObjectPropertyAxiom opAx : axioms

-- IrreflexiveObjectProperty axiom
tObjectPropertyAxiom opAx@(IrreflexiveObjectProperty anns opExpr) ms =
   M.insert ("ObjectProperty", fIdValue) (M.insert "characteristics" newAxioms m2) m1
   where
        fIdValue = case opExpr of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr
        m1 = tAnnotations anns . tObjectPropertyExpression True opExpr $ ms
        m2 = M.findWithDefault M.empty ("ObjectProperty", fIdValue) m1
        axioms = M.findWithDefault [] "characteristics" m2
        newAxioms = S.toList . S.fromList $ ObjectPropertyAxiom opAx : axioms

-- SymmetricObjectProperty axiom
tObjectPropertyAxiom opAx@(SymmetricObjectProperty anns opExpr) ms =
   M.insert ("ObjectProperty", fIdValue) (M.insert "characteristics" newAxioms m2) m1
   where
        fIdValue = case opExpr of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr
        m1 = tAnnotations anns . tObjectPropertyExpression True opExpr $ ms
        m2 = M.findWithDefault M.empty ("ObjectProperty", fIdValue) m1
        axioms = M.findWithDefault [] "characteristics" m2
        newAxioms = S.toList . S.fromList $ ObjectPropertyAxiom opAx : axioms

-- AsymmetricObjectProperty axiom
tObjectPropertyAxiom opAx@(AsymmetricObjectProperty anns opExpr) ms =
   M.insert ("ObjectProperty", fIdValue) (M.insert "characteristics" newAxioms m2) m1
   where
        fIdValue = case opExpr of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr
        m1 = tAnnotations anns . tObjectPropertyExpression True opExpr $ ms
        m2 = M.findWithDefault M.empty ("ObjectProperty", fIdValue) m1
        axioms = M.findWithDefault [] "characteristics" m2
        newAxioms = S.toList . S.fromList $ ObjectPropertyAxiom opAx : axioms

-- TransitiveObjectProperty axiom
tObjectPropertyAxiom opAx@(TransitiveObjectProperty anns opExpr) ms =
   M.insert ("ObjectProperty", fIdValue) (M.insert "characteristics" newAxioms m2) m1
   where
        fIdValue = case opExpr of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr
        m1 = tAnnotations anns . tObjectPropertyExpression True opExpr $ ms
        m2 = M.findWithDefault M.empty ("ObjectProperty", fIdValue) m1
        axioms = M.findWithDefault [] "characteristics" m2
        newAxioms = S.toList . S.fromList $ ObjectPropertyAxiom opAx : axioms


-- | transform DataProperty axioms
tDataPropertyAxiom :: DataPropertyAxiom -> MnchstrSntx -> MnchstrSntx
-- SubDataPropertyOf axiom
tDataPropertyAxiom dpAx@(SubDataPropertyOf anns iri1 iri2) ms =
    M.insert ("DataProperty", IriId iri1)
        (M.insert "subPropertyOf" newAxioms m2)  m1
    where
        m1 = tAnnotations anns . tDataPropertyExpressions [iri1, iri2] $ ms

        m2 = M.findWithDefault M.empty ("DataProperty", IriId iri1) m1
        axioms = M.findWithDefault [] "subPropertyOf" m2
        newAxioms = S.toList . S.fromList $ DataPropertyAxiom dpAx : axioms

-- | transform Class axiom
tClassAxiom :: ClassAxiom -> MnchstrSntx -> MnchstrSntx
-- SubClassOf axiom
tClassAxiom clAx@(SubClassOf anns subClExpr@(Expression iri) supClExpr) ms = 
    M.insert ("Class", IriId iri) (M.insert "subClassOf" newAxioms m2) m1
    where
        m1 = tClassExpression supClExpr . tAnnotations anns $ ms
        -- m1 = ms
        m2 = M.findWithDefault M.empty ("Class", IriId iri) m1
        axioms = M.findWithDefault [] "subClassOf" m2
        newAxioms = S.toList . S.fromList $ ClassAxiom clAx : axioms

-- EquivalentClasses axiom
tClassAxiom clAx@(EquivalentClasses anns
    [Expression iri1, Expression iri2]) ms =
    M.insert ("Class", IriId iri1) (M.insert "equivalentTo" newAxioms1 m1)
    . M.insert ("Class", IriId iri2) 
        (M.insert "equivalentTo" newAxioms2 m2) $ m'
    where
        m' = tAnnotations anns ms
        m1 = M.findWithDefault M.empty ("Class", IriId iri1) m'
        m2 = M.findWithDefault M.empty ("Class", IriId iri2) m'
        axioms1 = M.findWithDefault [] "equivalentTo" m1
        axioms2 = M.findWithDefault [] "equivalentTo" m2
        newAxioms1 = S.toList . S.fromList $ ClassAxiom clAx : axioms1
        newAxioms2 = S.toList . S.fromList
            $ (ClassAxiom . EquivalentClasses anns $
                [Expression iri2, Expression iri1]) : axioms2

tClassAxiom clAx@(EquivalentClasses anns [Expression iri, clExpr]) ms =
    M.insert ("Class", IriId iri) (M.insert "equivalentTo" newAxioms m1) $ m'
    where
        m' = tAnnotations anns . tClassExpression clExpr $ ms
        m1 = M.findWithDefault M.empty ("Class", IriId iri) m'
        axioms = M.findWithDefault [] "equivalentTo" m1
        newAxioms = S.toList . S.fromList $ ClassAxiom clAx : axioms

tClassAxiom clAx@(EquivalentClasses anns clExprs) ms =
    M.insert ("Misc", MiscId) (M.insert "equivalentClasses" newAxioms m1) $ m'
    where
        m' = tAnnotations anns . tClassExpressions clExprs $ ms
        m1 = M.findWithDefault M.empty ("Misc", MiscId) m'
        axioms = M.findWithDefault [] "equivalentClasses" m1
        newAxioms = S.toList . S.fromList $ ClassAxiom clAx : axioms

-- DisjointClasses axiom
tClassAxiom clAx@(DisjointClasses anns
    [Expression iri1, Expression iri2]) ms =
    M.insert ("Class", IriId iri1) (M.insert "disjointWith" newAxioms1 m1)
    . M.insert ("Class", IriId iri2) 
        (M.insert "disjointWith" newAxioms2 m2) $ m'
    where
        m' = tAnnotations anns ms
        m1 = M.findWithDefault M.empty ("Class", IriId iri1) m'
        m2 = M.findWithDefault M.empty ("Class", IriId iri2) m'
        axioms1 = M.findWithDefault [] "disjointWith" m1
        axioms2 = M.findWithDefault [] "disjointWith" m2
        newAxioms1 = S.toList . S.fromList $ ClassAxiom clAx : axioms1
        newAxioms2 = S.toList . S.fromList
            $ (ClassAxiom . DisjointClasses anns $
                [Expression iri2, Expression iri1]) : axioms2

tClassAxiom clAx@(DisjointClasses anns [Expression iri, clExpr]) ms =
    M.insert ("Class", IriId iri) (M.insert "disjointWith" newAxioms m1) $ m'
    where
        m' = tAnnotations anns . tClassExpression clExpr $ ms
        m1 = M.findWithDefault M.empty ("Class", IriId iri) m'
        axioms = M.findWithDefault [] "disjointWith" m1
        newAxioms = S.toList . S.fromList $ ClassAxiom clAx : axioms

tClassAxiom clAx@(DisjointClasses anns clExprs) ms =
    M.insert ("Misc", MiscId) (M.insert "disjointClasses" newAxioms m1) $ m'
    where
        m' = tAnnotations anns . tClassExpressions clExprs $ ms
        m1 = M.findWithDefault M.empty ("Misc", MiscId) m'
        axioms = M.findWithDefault [] "disjointClasses" m1
        newAxioms = S.toList . S.fromList $ ClassAxiom clAx : axioms

-- DisjointUnion axiom
tClassAxiom clAx@(DisjointUnion anns iri clExprs) ms =
    M.insert ("Class", IriId iri) (M.insert "disjointUnionOf" newAxioms m1) $ m'
    where
        m' = tAnnotations anns . tClassExpressions clExprs $ ms
        m1 = M.findWithDefault M.empty ("Class", IriId iri) m'
        axioms = M.findWithDefault [] "disjointUnionOf" m1
        newAxioms = S.toList . S.fromList $ ClassAxiom clAx : axioms

-- | transform HasKey axiom
tHasKey :: Axiom -> MnchstrSntx -> MnchstrSntx
tHasKey (HasKey anns (Expression iri) opExprs dpExprs) ms =
    M.insert ("Class", IriId iri) (M.insert "hasKey" newAxioms m1) $ m'
    where
        opExprs' = S.toList . S.fromList $ opExprs
        dpExprs' = S.toList . S.fromList $ dpExprs
        m' = tAnnotations anns . tObjectPropertyExpressions False opExprs'
            . tDataPropertyExpressions dpExprs' $ ms
        m1 = M.findWithDefault M.empty ("Class", IriId iri) m'
        axioms = M.findWithDefault [] "hasKey" m1
        newAxioms = S.toList . S.fromList $
            (HasKey anns (Expression iri) opExprs' dpExprs') : axioms

tHasKey (HasKey anns clExpr opExprs dpExprs) ms =
    tAnnotations anns . tClassExpression clExpr
    . tObjectPropertyExpressions False opExprs
    . tDataPropertyExpressions dpExprs $ ms

-- | transform Annotations
tAnnotations :: [Annotation] -> MnchstrSntx -> MnchstrSntx
tAnnotations = flip $ foldr tAnnotation

tAnnotation :: Annotation -> MnchstrSntx -> MnchstrSntx
tAnnotation (Annotation anns annProp annVal) ms =
    M.insert k (M.findWithDefault M.empty k m1) m1
    where
        k = ("AnnotationProperty", IriId annProp)
        m1 = tAnnotations anns . tAnnotationValue annVal $ ms

-- | transform AnnotationValue
tAnnotationValue :: AnnotationValue -> MnchstrSntx -> MnchstrSntx
tAnnotationValue (AnnAnInd ind) ms = tIndividual ind ms

tAnnotationValue (AnnValue iri) ms = ms --- ?

tAnnotationValue (AnnValLit lit) ms = tLiteral lit ms

-- | transform ClassExpression
tClassExpressions :: [ClassExpression] -> MnchstrSntx -> MnchstrSntx
tClassExpressions = flip $ foldr tClassExpression 

tClassExpression :: ClassExpression -> MnchstrSntx -> MnchstrSntx
tClassExpression (Expression iri) ms = 
    M.insert k (M.findWithDefault M.empty k ms) ms
    where k = ("Class", IriId iri)

tClassExpression (ObjectJunction _ clExprs) ms = tClassExpressions clExprs ms

tClassExpression (ObjectComplementOf clExpr) ms = tClassExpression clExpr ms

tClassExpression (ObjectOneOf inds) ms = tIndividuals inds ms

tClassExpression (ObjectValuesFrom _ obPropExpr clExpr) ms =
    tObjectPropertyExpression False obPropExpr
    . tClassExpression clExpr $ ms

tClassExpression (ObjectHasValue obPropExpr ind) ms =
    tObjectPropertyExpression False obPropExpr
    . tIndividual ind $ ms

tClassExpression (ObjectHasSelf obPropExpr) ms = 
    tObjectPropertyExpression False obPropExpr ms

tClassExpression (ObjectCardinality card) ms =
    case card of
        Cardinality ct n obPropExpr (Just clExpr) ->
            tObjectPropertyExpression False obPropExpr
            . tClassExpression clExpr $ ms
        Cardinality ct n obPropExpr Nothing ->
            tObjectPropertyExpression False obPropExpr ms

tClassExpression (DataValuesFrom qt iris dr) ms =
    tDataPropertyExpression (head iris) . tDataRange dr $ ms

tClassExpression (DataHasValue dpExpr lit) ms =
    tDataPropertyExpression dpExpr . tLiteral lit $ ms

tClassExpression (DataCardinality card) ms =
    case card of
        Cardinality ct n dpExpr (Just dr) ->
            tDataPropertyExpression dpExpr
            . tDataRange dr $ ms
        Cardinality ct n dpExpr Nothing ->
            tDataPropertyExpression dpExpr ms

-- | transform ObjectPropertyExpression
tObjectPropertyExpressions :: Bool -> [ObjectPropertyExpression]
    -> MnchstrSntx ->  MnchstrSntx
tObjectPropertyExpressions flag = flip $ foldr (tObjectPropertyExpression flag)

tObjectPropertyExpression :: Bool -> ObjectPropertyExpression
    -> MnchstrSntx -> MnchstrSntx
tObjectPropertyExpression _ (ObjectProp iri) ms =
    M.insert k (M.findWithDefault M.empty k ms) ms
    where k = ("ObjectProperty", IriId iri)

tObjectPropertyExpression True (ObjectInverseOf expr) ms =
    M.insert k2 (M.findWithDefault M.empty k2 m1) m1
    where 
        iri = obPropExprToIRI expr
        k1 = ("ObjectProperty", ObjInvOfId iri)
        k2 = ("ObjectProperty", IriId iri)
        m1 = M.insert k1 (M.findWithDefault M.empty k1 ms) ms

tObjectPropertyExpression False (ObjectInverseOf expr) ms =
    M.insert k (M.findWithDefault M.empty k ms) ms
    where k = ("ObjectProperty", IriId . obPropExprToIRI $ expr)

-- | transform DataRange
tDataRange :: DataRange -> MnchstrSntx -> MnchstrSntx
tDataRange (DataType dt fvs) ms =
    tDatatype dt . foldr (\x m -> tLiteral (snd x) m) ms $ fvs

tDataRange (DataJunction _ drs) ms = foldr tDataRange ms drs

tDataRange (DataComplementOf dr) ms = tDataRange dr ms

tDataRange (DataOneOf lits) ms = foldr tLiteral ms lits

-- | transform Datatype
tDatatype :: Datatype -> MnchstrSntx -> MnchstrSntx
tDatatype iri ms =
    M.insert k (M.findWithDefault M.empty k ms) ms
    where k = ("Datatype", IriId iri)

-- | transform Literal
tLiteral :: Literal -> MnchstrSntx -> MnchstrSntx
tLiteral (Literal _ t) ms = case t of
    Typed dt -> tDatatype dt ms
    Untyped _ ->  tDatatype plainDatatypeIRI ms
    where plainDatatypeIRI = IRI {
          iriScheme = ""
        , iriAuthority = Nothing
        , iriPath = mkId []
        , iriQuery = ""
        , iriFragment = "PlainLiteral"
        , prefixName = "rdf"
        , isAbbrev = False
        , isBlankNode = False
        , hasAngles = False
        , iriPos = nullRange
        , iFragment = "PlainLiteral"
    }

-- | transform DataPropertyExpression
tDataPropertyExpressions :: [DataPropertyExpression]
    -> MnchstrSntx -> MnchstrSntx
tDataPropertyExpressions = flip $ foldr tDataPropertyExpression

tDataPropertyExpression :: DataPropertyExpression
    -> MnchstrSntx -> MnchstrSntx
tDataPropertyExpression iri ms =
    M.insert k (M.findWithDefault M.empty k ms) ms
    where k = ("DataProperty", IriId iri)

-- | transform Individual
tIndividuals :: [Individual] -> MnchstrSntx -> MnchstrSntx
tIndividuals = flip $ foldr tIndividual

tIndividual :: Individual -> MnchstrSntx -> MnchstrSntx
tIndividual iri ms =
    M.insert k (M.findWithDefault M.empty k ms) ms
    where k = ("Individual", IriId iri)
    
------------- main printing part ----------------  

instance Pretty OntologyDocument where
    pretty (OntologyDocument prefDecls ont) = 
        (vcat . map pretty $ prefDecls)
        $++$ printOntology prefDecls ont

instance Pretty PrefixDeclaration where
    pretty (PrefixDeclaration prName iri) =
        hsep [keyword "Prefix:", text (prName ++ ":"), pretty iri]

printOntology :: [PrefixDeclaration] -> Ontology -> Doc
printOntology pds 
    (Ontology mOntIRI mVersionIRI importedDocs annotations axioms) =
        keyword "Ontology:"
        <+> ontIRI
        <+> versionIRI
        $++$ impDocs
        $++$ anns
        $++$ axs
    where
        versionIRI = maybe empty (printIRI pds) mVersionIRI
        ontIRI = maybe empty (\x -> printIRI pds x <+> versionIRI) mOntIRI
        impDocs = vcat . map
            (\x -> keyword "Import:" <+> printIRI pds x) $ importedDocs
        anns = printAnnotations pds 0 annotations
        ms = tAxioms axioms emptyMS
        axs = printMS pds ms 

-- | print Manchester Syntax
printMS :: [PrefixDeclaration] -> MnchstrSntx -> Doc
printMS pds ms = 
    vsep [objectPropertyFrames, dataPropertyFrames, annotationPropertyFrames
        , datatypeFrames, classFrames, individualFrames, miscFrame]
    where
        objectPropertyFrames = printOPFs pds 0 ms
        dataPropertyFrames = printDPFs pds 0 ms
        annotationPropertyFrames = printAPFs pds 0 ms
        datatypeFrames = printDFs pds 0 ms
        classFrames = printCFs pds 0 ms
        individualFrames = printIFs pds 0 ms
        miscFrame = printMF pds 0 ms

-------------------- Print Frames --------------------

-- | print Object Property Frames
printOPFs :: [PrefixDeclaration] -> Int -> MnchstrSntx -> Doc
printOPFs pds n ms
    | null headers = empty
    | otherwise = foldl ($++$) empty
        . map (\h -> printOPF pds n h $ M.findWithDefault M.empty h ms)
        $ headers
    where
        headers = filter ((=="ObjectProperty") . fst) . M.keys $ ms

-- | print Object Property Frame
printOPF :: [PrefixDeclaration] -> Int -> FrameId
    -> M.Map String [Axiom] -> Doc
printOPF pds n header body =
    vcat [tabs n <> keyword "ObjectProperty:" <+> hDoc
        , subPropOfDoc, subPropChainDoc, eqDoc, disjDoc
        , invDoc, domDoc, rangeDoc, charsDoc]
    where
        hDoc = case snd header of 
                IriId iri -> printIRI pds iri
                ObjInvOfId iri -> keyword "inverse" <+> printIRI pds iri

        subPropOfAxioms = M.findWithDefault [] "subPropertyOf" body
        subPropOfDoc = opAxiomsToDoc pds (n + 1) "SubPropertyOf:"
            . map unpackObjectPropertyAxiom $ subPropOfAxioms
        
        subPropChainAxioms = M.findWithDefault [] "subPropertyChain" body
        subPropChainDoc = opAxiomsToDoc pds (n + 1) "SubPropertyChain:"
            . map unpackObjectPropertyAxiom $ subPropChainAxioms

        eqAxioms = M.findWithDefault [] "equivalentTo" body
        eqDoc = opAxiomsToDoc pds (n + 1) "EquivalentTo:"
            . map unpackObjectPropertyAxiom $ eqAxioms

        disjAxioms = M.findWithDefault [] "disjointWith" body
        disjDoc = opAxiomsToDoc pds (n + 1) "DisjointWith:"
            . map unpackObjectPropertyAxiom $ disjAxioms

        invAxioms = M.findWithDefault [] "inverseOf" body
        invDoc = opAxiomsToDoc pds (n + 1) "InverseOf:"
            . map unpackObjectPropertyAxiom $ invAxioms

        domAxioms = M.findWithDefault [] "domain" body
        domDoc = opAxiomsToDoc pds (n + 1) "Domain:"
            . map unpackObjectPropertyAxiom $ domAxioms

        rangeAxioms = M.findWithDefault [] "range" body
        rangeDoc = opAxiomsToDoc pds (n + 1) "Range:"
            . map unpackObjectPropertyAxiom $ rangeAxioms

        charsAxioms = M.findWithDefault [] "characteristics" body
        charsDoc = opAxiomsToDoc pds (n + 1) "Characteristics:"
            . map unpackObjectPropertyAxiom $ charsAxioms

opAxiomsToDoc :: [PrefixDeclaration] -> Int -> String
    -> [ObjectPropertyAxiom] -> Doc
opAxiomsToDoc _ _ _ [] = empty

opAxiomsToDoc pds n "SubPropertyOf:" axioms =
    h $+$ (vcat . punctuate comma
        . map (\a -> tabs (n + 1) <> printSubPropOf pds a) $ axioms)
    where
        h = case axioms of
            [] -> empty
            _ -> tabs n <> keyword "SubPropertyOf:"

opAxiomsToDoc pds n "SubPropertyChain:" axioms =
    vsep
    . map (\d -> tabs n <> keyword "SubPropertyChain:" $+$ d)
    . map (\a -> tabs (n + 1) <> printSubPropChain pds a)
    $ axioms

opAxiomsToDoc pds n "EquivalentTo:" axioms =
    tabs n <> keyword "EquivalentTo:"
    $+$
    (vcat . map (printEqObProp pds (n + 1)) $ axioms)

opAxiomsToDoc pds n "DisjointWith:" axioms =
    tabs n <> keyword "DisjointWith:"
    $+$
    (vcat . map (printDisjObProp pds (n + 1)) $ axioms)

opAxiomsToDoc pds n "InverseOf:" axioms =
    tabs n <> keyword "InverseOf:"
    $+$
    (vcat . map (printInvObProp pds (n + 1)) $ axioms)

opAxiomsToDoc pds n "Domain:" axioms =
    tabs n <> keyword "Domain:"
    $+$
    (vcat . map (printObPropDom pds (n + 1)) $ axioms)

opAxiomsToDoc pds n "Range:" axioms =
    tabs n <> keyword "Range:"
    $+$
    (vcat . map (printObPropRange pds (n + 1)) $ axioms)

opAxiomsToDoc pds n "Characteristics:" axioms =
    tabs n <> keyword "Characteristics:"
    $+$
    (vcat . punctuate comma . map (printCharacteristics pds (n + 1)) $ axioms)

printSubPropOf :: [PrefixDeclaration] -> ObjectPropertyAxiom -> Doc
printSubPropOf pds (SubObjectPropertyOf anns 
    (SubObjPropExpr_obj _) opExpr) =
    printObjectPropertyExpression pds opExpr

printSubPropChain :: [PrefixDeclaration] -> ObjectPropertyAxiom -> Doc
printSubPropChain pds (SubObjectPropertyOf anns
    (SubObjPropExpr_exprchain opExprs) (ObjectProp iri)) =
    hcat . punctuate (keyword " o ")
    . map (printObjectPropertyExpression pds) $ opExprs

printEqObProp :: [PrefixDeclaration] -> Int -> ObjectPropertyAxiom -> Doc
printEqObProp pds n (EquivalentObjectProperties anns (_:es)) =
    printAnnotations pds (n + 1) anns
    $+$
    (vcat . punctuate comma
    . map (\e -> tabs (n + 1)
        <> printObjectPropertyExpression pds e) $ es)

printDisjObProp :: [PrefixDeclaration] -> Int -> ObjectPropertyAxiom -> Doc
printDisjObProp pds n (DisjointObjectProperties anns (_:es)) =
    printAnnotations pds (n + 1) anns
    $+$
    (vcat . punctuate comma
    . map (\e -> tabs (n + 1)
        <> printObjectPropertyExpression pds e) $ es)

printInvObProp :: [PrefixDeclaration] -> Int -> ObjectPropertyAxiom -> Doc
printInvObProp pds n (InverseObjectProperties anns _ opExpr) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printObjectPropertyExpression pds opExpr

printObPropDom :: [PrefixDeclaration] -> Int -> ObjectPropertyAxiom -> Doc
printObPropDom pds n (ObjectPropertyDomain anns _ clExpr) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printClassExpression pds clExpr

printObPropRange :: [PrefixDeclaration] -> Int -> ObjectPropertyAxiom -> Doc
printObPropRange pds n (ObjectPropertyRange anns _ clExpr) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printClassExpression pds clExpr

printCharacteristics :: [PrefixDeclaration] -> Int -> ObjectPropertyAxiom -> Doc
printCharacteristics pds n (FunctionalObjectProperty anns _) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> keyword "Functional"

printCharacteristics pds n (InverseFunctionalObjectProperty anns _) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> keyword "InverseFunctional"

printCharacteristics pds n (ReflexiveObjectProperty anns _) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> keyword "Reflexive"

printCharacteristics pds n (IrreflexiveObjectProperty anns _) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> keyword "Irreflexive"

printCharacteristics pds n (SymmetricObjectProperty anns _) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> keyword "Symmetric"

printCharacteristics pds n (AsymmetricObjectProperty anns _) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> keyword "Asymmetric"

printCharacteristics pds n (TransitiveObjectProperty anns _) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> keyword "Transitive"

unpackObjectPropertyAxiom :: Axiom -> ObjectPropertyAxiom
unpackObjectPropertyAxiom (ObjectPropertyAxiom a) = a

-- | print Data Property Frames
printDPFs :: [PrefixDeclaration] -> Int -> MnchstrSntx -> Doc
printDPFs pds n ms 
    | null headers = empty
    | otherwise = foldl ($++$) empty
        . map (\h -> printDPF pds n h $ M.findWithDefault M.empty h ms)
        $ headers
    where
        headers = filter ((=="DataProperty") . fst) . M.keys $ ms

-- | print Data Property Frame
printDPF :: [PrefixDeclaration] -> Int -> FrameId
    -> M.Map String [Axiom] -> Doc
printDPF pds n header body = 
    vcat[tabs n <> keyword "DataProperty:" <+> printIRI pds iri]
    where
        IriId iri = snd header

        -- subDataPropOfAxioms = M.findWithDefault [] "subDataPropertyOf" body
        -- subDataPropOfDoc = dpAxiomsToDoc pds (n + 1) "SubDataPropertyOf:"
        --     . map unpackDataPropertyAxiom $ subPropOfAxioms

dpAxiomsToDoc :: [PrefixDeclaration] -> Int -> String
    -> [DataPropertyAxiom] -> Doc
dpAxiomsToDoc _ _ _ [] = empty

unpackDataPropertyAxiom :: Axiom -> DataPropertyAxiom
unpackDataPropertyAxiom (DataPropertyAxiom a) = a

-- | print Annotation Property Frames
printAPFs :: [PrefixDeclaration] -> Int -> MnchstrSntx -> Doc
printAPFs pds n ms
    | null headers = empty
    | otherwise = foldl ($++$) empty
        . map (\h -> printAPF pds n h $ M.findWithDefault M.empty h ms)
        $ headers
    where
        headers = filter ((=="AnnotationProperty") . fst) . M.keys $ ms

-- | print Annotation Property Frame
printAPF :: [PrefixDeclaration] -> Int -> FrameId
    -> M.Map String [Axiom] -> Doc
printAPF pds n header body = 
    tabs n <> keyword "AnnotationProperty:" <+> printIRI pds iri
    where
        IriId iri = snd header

-- | print Datatype Frames
printDFs :: [PrefixDeclaration] -> Int -> MnchstrSntx -> Doc
printDFs pds n ms
    | null headers = empty
    | otherwise = foldl ($++$) empty
        . map (\h -> printDF pds n h $ M.findWithDefault M.empty h ms)
        $ headers
    where
        headers = filter ((=="Datatype") . fst) . M.keys $ ms

-- | print Datatype Frame
printDF :: [PrefixDeclaration] -> Int -> FrameId
    -> M.Map String [Axiom] -> Doc
printDF pds n header body =
    tabs n <> keyword "Datatype:" <+> printMSDatatype pds iri
    where
        IriId iri = snd header

printMSDatatype :: [PrefixDeclaration] -> IRI -> Doc
printMSDatatype pds iri
    | isAbbrev iri && prefixName iri == "xsd"
        && iFragment iri `elem` ["integer", "decimal", "float"]
        = text ("xsd:" ++ iFragment iri)
    | otherwise = printIRI pds iri

-- | print Class Frames
printCFs :: [PrefixDeclaration] -> Int -> MnchstrSntx -> Doc
printCFs pds n ms
    | null headers = empty
    | otherwise = foldl ($++$) empty
        . map (\h -> printCF pds n h $ M.findWithDefault M.empty h ms)
        $ headers 
    where
        headers = filter ((=="Class") . fst) . M.keys $ ms

-- | print Class Frame
printCF :: [PrefixDeclaration] -> Int -> FrameId
    -> M.Map String [Axiom] -> Doc
printCF pds n header body =
    vcat [tabs n <> keyword "Class:" <+> printIRI pds iri
        , scoDoc, eqDoc, disjDoc, disjuDoc, haskDoc]
    where
        IriId iri = snd header
        -- annAxioms = M.findWithDefault [] "annotation" body
        scoAxioms = M.findWithDefault [] "subClassOf" body
        scoDoc = classAxiomsToDoc pds (n + 1) "SubClassOf:" scoAxioms

        eqAxioms = M.findWithDefault [] "equivalentTo" body
        eqDoc = classAxiomsToDoc pds (n + 1) "EquivalentTo:" eqAxioms

        disjAxioms = M.findWithDefault [] "disjointWith" body
        disjDoc = classAxiomsToDoc pds (n + 1) "DisjointWith:" disjAxioms

        disjuAxioms = M.findWithDefault [] "disjointUnionOf" body
        disjuDoc = classAxiomsToDoc pds (n + 1) "DisjointUnionOf:" disjuAxioms

        haskAxioms = M.findWithDefault [] "hasKey" body
        haskDoc = hasKeyAxiomsToCFDoc pds (n + 1) "HasKey:" haskAxioms


classAxiomsToDoc :: [PrefixDeclaration] -> Int -> String -> [Axiom] -> Doc
classAxiomsToDoc pds n header axioms = case axioms of
    [] -> empty
    _ ->  tabs n <> keyword header
        $+$ (printClassAxiomsVer pds (n + 1)
            . map unpackClassAxiom
            $ axioms)

hasKeyAxiomsToCFDoc :: [PrefixDeclaration] -> Int -> String -> [Axiom] -> Doc
hasKeyAxiomsToCFDoc pds n header axioms =  
    foldr (\ax d -> printHasKeyAxiom pds n header ax $+$ d) empty axioms

unpackClassAxiom :: Axiom -> ClassAxiom
unpackClassAxiom (ClassAxiom a) = a

-- | print HasKey axiom
printHasKeyAxiom :: [PrefixDeclaration] -> Int -> String -> Axiom -> Doc
printHasKeyAxiom pds n header (HasKey anns _ opExprs dpExprs) =
    tabs n <> keyword header
    $+$ printAnnotations pds (n + 1) anns
    $+$ (vcat . punctuate comma $ [opExprsDocs, dpExprsDocs])
    where
        opExprsDocs = vcat . punctuate comma
            . map (\e -> tabs (n + 1) <> 
                        printObjectPropertyExpression pds e) $ opExprs
        dpExprsDocs = vcat . punctuate comma
            . map (\e -> tabs (n + 1) <> printIRI pds e) $ dpExprs
         
-- | print ClassAxioms
printClassAxiomsHor :: [PrefixDeclaration] -> Int -> [ClassAxiom] -> Doc
printClassAxiomsHor pds n axioms =
    tabs n <> (hsep . punctuate comma . map (printClassAxiom pds 0) $ axioms)

printClassAxiomsVer :: [PrefixDeclaration] -> Int -> [ClassAxiom] -> Doc
printClassAxiomsVer pds n =
    vcat . punctuate comma . map (printClassAxiom pds n)

printClassAxiom :: [PrefixDeclaration] -> Int -> ClassAxiom -> Doc
-- subClassOf axiom
printClassAxiom pds n (SubClassOf anns iri supClExpr) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printClassExpression pds supClExpr

-- EquivalentClasses axiom
printClassAxiom pds n (EquivalentClasses anns [_, clExpr]) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printClassExpression pds clExpr

printClassAxiom pds n (EquivalentClasses anns clExprs) = 
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printClassExpressionsHor pds clExprs

-- DisjointClasses axiom
printClassAxiom pds n (DisjointClasses anns [_, clExpr]) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printClassExpression pds clExpr

printClassAxiom pds n (DisjointClasses anns clExprs) = 
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printClassExpressionsHor pds clExprs

-- DisjointUnion axiom
printClassAxiom pds n (DisjointUnion anns iri clExprs) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printClassExpressionsHor pds clExprs

-- | print Individual Frames
printIFs :: [PrefixDeclaration] -> Int -> MnchstrSntx -> Doc
printIFs pds n ms
    | null headers = empty
    | otherwise = foldl ($++$) empty
        . map (\h -> printIF pds n h $ M.findWithDefault M.empty h ms)
        $ headers 
    where
        headers = filter ((=="Individual") . fst) . M.keys $ ms

-- | print Individual Frame
printIF :: [PrefixDeclaration] -> Int -> FrameId
    -> M.Map String [Axiom] -> Doc
printIF pds n header body = 
    vcat [tabs n <> keyword "Individual:" <+> printIRI pds iri]
    where 
        IriId iri = snd header

-- | print Misc Frame
printMF :: [PrefixDeclaration] -> Int -> MnchstrSntx -> Doc
printMF pds n ms
    | M.null mRoot = empty
    | otherwise = 
        vcat [eqClsDoc, disjClsDoc, eqObPropsDoc, disjObPropsDoc]
    where
        mRoot = M.findWithDefault M.empty ("Misc", MiscId) ms
        eqClsAxioms = M.findWithDefault [] "equivalentClasses" mRoot
        eqClsDoc = eqClsAxiomsToMFDoc pds n eqClsAxioms

        disjClsAxioms = M.findWithDefault [] "disjointClasses" mRoot
        disjClsDoc = disjClsAxiomsToMFDoc pds n disjClsAxioms

        eqObPropsAxioms = M.findWithDefault [] "equivalentProperties" mRoot
        eqObPropsDoc = eqObPropsAxiomsToMFDoc pds n eqObPropsAxioms

        disjObPropsAxioms = M.findWithDefault [] "disjointProperties" mRoot
        disjObPropsDoc = disjObPropsAxiomsToMFDoc pds n disjObPropsAxioms

eqClsAxiomsToMFDoc :: [PrefixDeclaration] -> Int -> [Axiom] -> Doc
eqClsAxiomsToMFDoc pds n [] = empty
eqClsAxiomsToMFDoc pds n axioms =
    vsep docsWithHeaders
    where
        classAxioms = map unpackClassAxiom axioms
        bodyDocs = map (printClassAxiom pds (n + 1)) classAxioms
        docsWithHeaders = map (\d -> keyword "EquivalentClases:" $+$ d) bodyDocs

disjClsAxiomsToMFDoc :: [PrefixDeclaration] -> Int -> [Axiom] -> Doc
disjClsAxiomsToMFDoc pds n [] = empty
disjClsAxiomsToMFDoc pds n axioms =
    vsep docsWithHeaders
    where
        classAxioms = map unpackClassAxiom axioms
        bodyDocs = map (printClassAxiom pds (n + 1)) classAxioms
        docsWithHeaders = map (\d -> keyword "DisjointClasses:" $+$ d) bodyDocs

eqObPropsAxiomsToMFDoc :: [PrefixDeclaration] -> Int -> [Axiom] -> Doc
eqObPropsAxiomsToMFDoc pds n [] = empty
eqObPropsAxiomsToMFDoc pds n axioms =
    vsep docsWithHeaders
    where 
        opAxioms = map unpackObjectPropertyAxiom axioms
        bodyDocs = map (printObPropAxiomMF pds (n + 1)) opAxioms
        docsWithHeaders =
            map (\d -> keyword "EquivalentProperties:" $+$ d) bodyDocs

disjObPropsAxiomsToMFDoc :: [PrefixDeclaration] -> Int -> [Axiom] -> Doc
disjObPropsAxiomsToMFDoc pds n [] = empty
disjObPropsAxiomsToMFDoc pds n axioms =
    vsep docsWithHeaders
    where 
        opAxioms = map unpackObjectPropertyAxiom axioms
        bodyDocs = map (printObPropAxiomMF pds (n + 1)) opAxioms
        docsWithHeaders =
            map (\d -> keyword "DisjointProperties:" $+$ d) bodyDocs

printObPropAxiomMF :: [PrefixDeclaration] -> Int -> ObjectPropertyAxiom -> Doc
printObPropAxiomMF pds n (EquivalentObjectProperties anns opExprs) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printObjectPropertyExpressionsHor pds opExprs 

printObPropAxiomMF pds n (DisjointObjectProperties anns opExprs) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printObjectPropertyExpressionsHor pds opExprs 

-- | print Annotations
printAnnotationValue :: [PrefixDeclaration] -> AnnotationValue -> Doc
printAnnotationValue pds anVal = case anVal of
    AnnAnInd anInd -> printIRI pds anInd
    AnnValue iri -> printIRI pds iri
    AnnValLit lit -> printLiteral pds lit

printAnnotation :: [PrefixDeclaration] -> Int -> Annotation -> Doc
printAnnotation pds n (Annotation anns annProperty annValue) =
    printAnnotations pds (n + 1) anns
    $+$
    (hsep $ [tabs n, docAnnProp, docAnnVal])
    where
        docAnnProp = printIRI pds annProperty
        docAnnVal = printAnnotationValue pds annValue

printAnnotations :: [PrefixDeclaration] -> Int -> Annotations -> Doc
printAnnotations pds _ [] = empty
printAnnotations pds n anns =
    tabs n <> keyword "Annotations:"
    $+$
    (vcat . punctuate comma . map (printAnnotation pds (n + 1)) $ anns)

-- | print IRI
printIRI :: [PrefixDeclaration] -> IRI -> Doc
printIRI pds iri
    | isAbbrev iri && containsPrefix pds prefName =
        text (prefName ++ ":" ++ (iFragment iri))
    | otherwise = pretty iri
  where prefName = prefixName iri

printDataIRI :: [PrefixDeclaration] -> IRI -> Doc
printDataIRI pds q
    | isDatatypeKey q = text $ showIRI $ setDatatypePrefix q
    | otherwise = printIRI pds q

containsPrefix :: [PrefixDeclaration] -> String -> Bool
containsPrefix [] _ = False
containsPrefix ((PrefixDeclaration name _):pds) prefName
    | name == prefName = True
    | otherwise = containsPrefix pds prefName

-- | print Literal
printLiteral :: [PrefixDeclaration] -> Literal -> Doc
printLiteral pds (Literal lexi ty) =
    case ty of
        Untyped tag -> printUntypedLiteral lexi tag
        Typed iri -> printTypedLiteral pds lexi iri

printUntypedLiteral :: String -> Maybe String -> Doc
printUntypedLiteral lexi tag = 
    plainText ('"' : escapeString lexi ++ "\"") 
    <> literalTail
    where
        literalTail = case tag of
            Nothing -> empty
            Just tg -> text asP <> text tg

printTypedLiteral :: [PrefixDeclaration] -> String -> IRI -> Doc 
printTypedLiteral pds lexi iri
    | isAbbrev iri && pn == "xsd" && iFrag == "float" =
        plainText (escapeString lexi) <> text "f"
    | isAbbrev iri && pn == "xsd" && iFrag `elem` ["integer", "decimal"] =
        plainText . escapeString $ lexi
    | otherwise = plainText ('"' : escapeString lexi ++ "\"")
        <> text "^^" <> printIRI pds iri
    where
        pn = prefixName iri
        iFrag = iFragment iri

escapeString ::  String -> String
escapeString [] = []
escapeString ('"':s) = '\\' : '"' : escapeString s
escapeString ('\\':s) = '\\' : '\\' : escapeString s
escapeString (c:s) = c : escapeString s 

---------------- | print ObjectPropertyExpression
printObjectPropertyExpressionsVer :: [PrefixDeclaration]
    -> [ObjectPropertyExpression] -> Doc
printObjectPropertyExpressionsVer pds =
    vcat . punctuate comma . map (printObjectPropertyExpression pds)

printObjectPropertyExpressionsHor :: [PrefixDeclaration]
    -> [ObjectPropertyExpression] -> Doc
printObjectPropertyExpressionsHor pds =
    hsep . punctuate comma . map (printObjectPropertyExpression pds)

printObjectPropertyExpression :: [PrefixDeclaration]
    -> ObjectPropertyExpression -> Doc
printObjectPropertyExpression pds obExpr =
    case obExpr of
        ObjectProp ou -> printIRI pds ou
        ObjectInverseOf iopExp -> 
            keyword "inverse"
            <+> printObjectPropertyExpression pds iopExp

---------------- | print DataRange
printFV :: [PrefixDeclaration] -> (ConstrainingFacet, RestrictionValue) -> Doc
printFV pds (facet, restValue) =
    text (fromCF facet) <+> printLiteral pds restValue

fromCF :: ConstrainingFacet -> String
fromCF f
    | isAbbrev f && prefixName f == "xsd"
        && (iFragment f) `elem` ["length", "minLength", "maxLength", "pattern"]
            = iFragment f
    | isAbbrev f && prefixName f == "rdf" && iFragment f == "langRange"
        = "langRange"
    | isAbbrev f && prefixName f == "xsd" && iFragment f == "minInclusive"
        = "<="
    | isAbbrev f && prefixName f == "xsd" && iFragment f == "minExclusive"
        = "<"
    | isAbbrev f && prefixName f == "xsd" && iFragment f == "maxInclusive"
        = ">="
    | isAbbrev f && prefixName f == "xsd" && iFragment f == "maxExclusive"
        = ">"
    | hasFullIRI f = showIRICompact f
    | otherwise = show $ iriPath f

printDataRange :: [PrefixDeclaration] -> DataRange -> Doc
printDataRange pds dr = case dr of
    DataType dtype l -> printIRI pds dtype <+>
        if null l then empty else brackets $ sepByCommas $ map (printFV pds) l
    DataComplementOf drange -> keyword "not" <+> printDataRange pds drange
    DataOneOf constList ->
        specBraces . fsep . punctuate comma . map (printLiteral pds) $ constList
    DataJunction ty drlist -> let
      k = case ty of
          UnionOf -> "or"
          IntersectionOf -> "and"
      in fsep $ prepPunctuate (keyword k <> space)
            $ map (printDataRange pds) drlist

---------------- | print ClassExpression
printClassExpressionsHor :: [PrefixDeclaration] -> [ClassExpression] -> Doc
printClassExpressionsHor pds =
    hsep . punctuate comma . map (printClassExpression pds)

printClassExpressionsVer :: [PrefixDeclaration] -> [ClassExpression] -> Doc
printClassExpressionsVer pds =
    vcat . punctuate comma . map (printClassExpression pds)

printClassExpression :: [PrefixDeclaration] -> ClassExpression -> Doc
printClassExpression pds expr = case expr of 
    Expression ocUri -> printIRI pds ocUri
    ObjectJunction ty ds -> let
        k = case ty of
            UnionOf -> "or"
            IntersectionOf -> "and"
        in fsep . prepPunctuate (keyword k <> space)
                . map (printPrimary pds) $ ds
    ObjectComplementOf d -> keyword "not" <+> printPrimary pds d
    ObjectOneOf indUriList ->
        specBraces . fsep . punctuate comma . map (printIRI pds) $ indUriList
    ObjectValuesFrom ty opExp d ->
        printObjectPropertyExpression pds opExp
        <+> quantifierType ty
        <+> printPrimary pds d
    ObjectHasSelf opExp ->
        printObjectPropertyExpression pds opExp <+> keyword "Self"
    ObjectHasValue opExp indUri ->
        printObjectPropertyExpression pds opExp 
        <+> keyword "value" <+> printIRI pds indUri
    ObjectCardinality (Cardinality ty card opExp maybeDesc) ->
        printObjectPropertyExpression pds opExp <+> cardinalityType ty
        <+> text (show card)
        <+> maybe (keyword "owl:Thing") (printPrimary pds) maybeDesc
    DataValuesFrom ty dpExp dRange ->
        printIRI pds (head dpExp) <+> quantifierType ty
        <+> printDataRange pds dRange
    DataHasValue dpExp cons ->
        printIRI pds dpExp <+> keyword "value" <+> printLiteral pds cons
    DataCardinality (Cardinality ty card dpExp maybeRange) ->
        printIRI pds dpExp <+> cardinalityType ty 
        <+> text (show card)
        <+> maybe empty (printDataRange pds) maybeRange

printPrimary :: [PrefixDeclaration] -> ClassExpression -> Doc
printPrimary pds d = 
    let dd = printClassExpression pds d
    in case d of
        Expression _ -> dd
        ObjectOneOf{} -> dd
        _ -> parens dd

quantifierType :: QuantifierType -> Doc
quantifierType = keyword . showQuantifierType

cardinalityType :: CardinalityType -> Doc
cardinalityType = keyword . showCardinalityType

