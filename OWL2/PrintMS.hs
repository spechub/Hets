module OWL2.PrintMS where

import qualified Data.Map as M
import qualified Data.Set as S

import Common.Doc
import Common.DocUtils
import Common.Keywords
import Common.IRI
import Common.GlobalAnnotations as GA (PrefixMap)

import OWL2.AS
import OWL2.Keywords
import OWL2.ColonKeywords

----- auxiliary MS data structures and transformations functions to MS -----
type Annotations = [Annotation]

data FrameIdValue = 
      IriId IRI
    | ObjInvOfId IRI
    | MiscId
    | RuleId
    deriving(Show, Eq, Ord)

data FrameType =
      DatatypeFrame
    | ClassFrame
    | ObjectPropertyFrame
    | DataPropertyFrame
    | AnnotationPropertyFrame
    | IndividualFrame
    | MiscFrame
    | RuleFrame
    deriving(Show, Eq, Ord, Enum, Bounded)

data FrameSectionType =
      AnnotationsSection
    | EquivalentToSection
    | SubClassOfSection
    | DisjointWithSection
    | DisjointUnionOfSection
    | HasKeySection
    | DomainSection
    | RangeSection
    | CharacteristicsSection
    | SubPropertyOfSection
    | InverseOfSection
    | SubPropertyChainSection
    | TypesSection
    | FactsSection
    | SameAsSection
    | DifferentFromSection
    | EquivalentClassesSection
    | DisjointClassesSection
    | EquivalentDataPropertiesSection
    | EquivalentObjectPropertiesSection
    | DisjointDataPropertiesSection
    | DisjointObjectPropertiesSection
    | SameIndividualSection
    | DifferentIndividualsSection
    | RuleSection
    deriving(Show, Eq, Ord)

type FrameId = (FrameType, FrameIdValue)
type Frame = M.Map FrameSectionType [Axiom]
type MnchstrSntx = M.Map FrameId Frame

-- | function to extract IRI from ObjectInverseOf
obPropExprToIRI :: ObjectPropertyExpression -> IRI
obPropExprToIRI (ObjectProp iri) = iri
obPropExprToIRI (ObjectInverseOf obExpr) = obPropExprToIRI obExpr 

emptyMS :: MnchstrSntx
emptyMS = M.empty

tabs :: Int -> Doc
tabs n
    | n < 1 = empty
    | otherwise = text ['\t' | _ <- [1..n]]

-- transfromation functions, static analysis
-- From AS to intermediate MS
-- | transform Axioms
tAxioms :: [Axiom] -> MnchstrSntx -> MnchstrSntx
tAxioms = flip $ foldl (\m a -> tAxiom a m) 

-- | transform Axiom
tAxiom :: Axiom -> MnchstrSntx -> MnchstrSntx
tAxiom axiom ms = case axiom of
    Declaration {} -> tDeclaration axiom ms
    ClassAxiom ca -> tClassAxiom ca ms
    ObjectPropertyAxiom opa -> tObjectPropertyAxiom opa ms
    DataPropertyAxiom dpa -> tDataPropertyAxiom dpa ms
    DatatypeDefinition {} -> tDatatypeDefinition axiom ms
    Assertion a -> tAssertion a ms
    AnnotationAxiom a -> tAnnotationAxiom a ms
    HasKey {} -> tHasKey axiom ms
    Rule ruel-> tRule ruel ms
    DGAxiom _ _ _ _ _ -> ms

-- | transform Declaration
tDeclaration :: Axiom -> MnchstrSntx -> MnchstrSntx
tDeclaration (Declaration anns entity) =
    tAddDecAnnAssertions entity anns
    . tEntity entity . tAnnotations anns

tDeclaration _ = id

tAddDecAnnAssertions :: Entity -> Annotations -> MnchstrSntx -> MnchstrSntx
tAddDecAnnAssertions entity =
    flip $ foldl (\m ann -> tAddDecAnnAssertion entity ann m)

tAddDecAnnAssertion :: Entity -> Annotation -> MnchstrSntx -> MnchstrSntx
tAddDecAnnAssertion entity (Annotation anns prop value) ms =
    M.insert k (M.insert AnnotationsSection newAxioms m1) ms
    where
        k = (frameType, IriId frameIRI)

        frameIRI = cutIRI entity
        frameType = case entityKind entity of
            Class -> ClassFrame
            Datatype -> DatatypeFrame
            ObjectProperty -> ObjectPropertyFrame
            DataProperty -> DataPropertyFrame
            AnnotationProperty -> AnnotationPropertyFrame
            NamedIndividual -> IndividualFrame

        m1 = M.findWithDefault M.empty k ms
        axs = M.findWithDefault [] AnnotationsSection m1
        newAxiom = AnnotationAxiom
            $ AnnotationAssertion anns prop (AnnSubIri frameIRI) value
        newAxioms = newAxiom : axs

-- | transform Entity
tEntity :: Entity -> MnchstrSntx -> MnchstrSntx
tEntity entity ms = case (entityKind entity) of
    Datatype ->
        if M.notMember (DatatypeFrame, IriId iri) ms
            then M.insert (DatatypeFrame, IriId iri) M.empty ms
            else ms

    Class -> 
        if M.notMember (ClassFrame, IriId iri) ms
            then M.insert (ClassFrame, IriId iri) M.empty ms
            else ms

    ObjectProperty ->
        if M.notMember (ObjectPropertyFrame, IriId iri) ms
            then M.insert (ObjectPropertyFrame, IriId iri) M.empty ms
            else ms

    DataProperty -> 
        if M.notMember (DataPropertyFrame, IriId iri) ms
            then M.insert (DataPropertyFrame, IriId iri) M.empty ms
            else ms

    AnnotationProperty ->
        if M.notMember (AnnotationPropertyFrame, IriId iri) ms
            then M.insert (AnnotationPropertyFrame, IriId iri) M.empty ms
            else ms
    
    NamedIndividual ->
        if M.notMember (IndividualFrame, IriId iri) ms
            then M.insert (IndividualFrame, IriId iri) M.empty ms
            else ms

    where iri = cutIRI entity

-- | transform ObjectProperty axiom
tObjectPropertyAxiom :: ObjectPropertyAxiom -> MnchstrSntx -> MnchstrSntx
-- SubObjectPropertyOf axiom
tObjectPropertyAxiom opAx@(SubObjectPropertyOf anns 
    (SubObjPropExpr_obj opExpr1) opExpr2) ms =
    M.insert k (M.insert SubPropertyOfSection newAxioms m2) m1
    where
        fIdValue = case opExpr1 of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr

        k = (ObjectPropertyFrame, fIdValue)
        m1 = tAnnotations anns . tObjectPropertyExpression True opExpr1 
            .tObjectPropertyExpression False opExpr2 $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] SubPropertyOfSection m2
        newAxioms = ObjectPropertyAxiom opAx : axs

tObjectPropertyAxiom opAx@(SubObjectPropertyOf anns
    (SubObjPropExpr_exprchain opExprs) (ObjectProp iri)) ms =
    M.insert k (M.insert SubPropertyChainSection newAxioms m2) m1
    where
        k = (ObjectPropertyFrame, IriId iri)
        m1 = tAnnotations anns . tObjectPropertyExpressions False opExprs $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] SubPropertyChainSection m2
        newAxioms = ObjectPropertyAxiom opAx : axs

tObjectPropertyAxiom (SubObjectPropertyOf anns
    (SubObjPropExpr_exprchain opExprs) opExpr) ms =
    tAnnotations anns . tObjectPropertyExpressions False opExprs
    . tObjectPropertyExpression False opExpr $ ms

-- EquivalentObjectProperties axiom
tObjectPropertyAxiom opAx@(EquivalentObjectProperties anns
    [opExpr1, opExpr2]) ms =
    M.insert k1 (M.insert EquivalentToSection newAxioms1 m1)
    . M.insert k2 (M.insert EquivalentToSection newAxioms2 m2) $ m'
    where
        fIdValue1 = case opExpr1 of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr

        fIdValue2 = case opExpr2 of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr

        k1 = (ObjectPropertyFrame, fIdValue1)
        k2 = (ObjectPropertyFrame, fIdValue2)
        m' = tAnnotations anns ms
        m1 = M.findWithDefault M.empty k1 m'
        m2 = M.findWithDefault M.empty k2 m'
        axioms1 = M.findWithDefault [] EquivalentToSection m1
        axioms2 = M.findWithDefault [] EquivalentToSection m2
        newAx = EquivalentObjectProperties anns $ [opExpr2, opExpr1]
        newAxioms1 = ObjectPropertyAxiom opAx : axioms1
        newAxioms2 = ObjectPropertyAxiom newAx : axioms2

tObjectPropertyAxiom opAx@(EquivalentObjectProperties anns opExprs) ms =
    M.insert k (M.insert EquivalentObjectPropertiesSection newAxioms m1) $ m'
    where
        k = (MiscFrame, MiscId)
        m' = tAnnotations anns . tObjectPropertyExpressions True opExprs $ ms
        m1 = M.findWithDefault M.empty k m'
        axs = M.findWithDefault [] EquivalentObjectPropertiesSection m1
        newAxioms = ObjectPropertyAxiom opAx : axs

-- DisjointObjectProperties axiom
tObjectPropertyAxiom opAx@(DisjointObjectProperties anns
    [opExpr1, opExpr2]) ms =
    M.insert k1 (M.insert DisjointWithSection newAxioms1 m1)
    . M.insert k2 (M.insert DisjointWithSection newAxioms2 m2) $ m'
    where
        fIdValue1 = case opExpr1 of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr

        fIdValue2 = case opExpr2 of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr

        k1 = (ObjectPropertyFrame, fIdValue1)
        k2 = (ObjectPropertyFrame, fIdValue2)
        m' = tAnnotations anns ms
        m1 = M.findWithDefault M.empty k1 m'
        m2 = M.findWithDefault M.empty k2 m'
        axioms1 = M.findWithDefault [] DisjointWithSection m1
        axioms2 = M.findWithDefault [] DisjointWithSection m2
        newAx = DisjointObjectProperties anns $ [opExpr2, opExpr1]
        newAxioms1 = ObjectPropertyAxiom opAx : axioms1
        newAxioms2 = ObjectPropertyAxiom newAx : axioms2

tObjectPropertyAxiom opAx@(DisjointObjectProperties anns opExprs) ms =
    M.insert k (M.insert DisjointObjectPropertiesSection newAxioms m1) $ m'
    where
        k = (MiscFrame, MiscId)
        m' = tAnnotations anns . tObjectPropertyExpressions True opExprs $ ms
        m1 = M.findWithDefault M.empty k m'
        axs = M.findWithDefault [] DisjointObjectPropertiesSection m1
        newAxioms = ObjectPropertyAxiom opAx : axs

-- InverseObjectProperties axiom
tObjectPropertyAxiom opAx@(InverseObjectProperties anns opExpr1 opExpr2) ms =
    M.insert k1 (M.insert InverseOfSection newAxioms1 m1)
    . M.insert k2 (M.insert InverseOfSection newAxioms2 m2) $ m'
    where
        fIdValue1 = case opExpr1 of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr

        fIdValue2 = case opExpr2 of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr

        k1 = (ObjectPropertyFrame, fIdValue1)
        k2 = (ObjectPropertyFrame, fIdValue2)
        m' = tAnnotations anns
            . tObjectPropertyExpressions True [opExpr1, opExpr2] $ ms
        m1 = M.findWithDefault M.empty k1 m'
        m2 = M.findWithDefault M.empty k2 m'
        axioms1 = M.findWithDefault [] InverseOfSection m1
        axioms2 = M.findWithDefault [] InverseOfSection m2
        newAx = InverseObjectProperties anns opExpr2 opExpr1
        newAxioms1 = ObjectPropertyAxiom opAx : axioms1
        newAxioms2 = ObjectPropertyAxiom newAx : axioms2

-- ObjectPropertyDomain axiom
tObjectPropertyAxiom opAx@(ObjectPropertyDomain anns opExpr clExpr) ms =
   M.insert k (M.insert DomainSection newAxioms m2) m1
   where
        fIdValue = case opExpr of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr

        k = (ObjectPropertyFrame, fIdValue)
        m1 = tAnnotations anns . tObjectPropertyExpression True opExpr
            . tClassExpression clExpr $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] DomainSection m2
        newAxioms = ObjectPropertyAxiom opAx : axs

-- ObjectPropertyRange axiom
tObjectPropertyAxiom opAx@(ObjectPropertyRange anns opExpr clExpr) ms =
   M.insert k (M.insert RangeSection newAxioms m2) m1
   where
        fIdValue = case opExpr of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr

        k = (ObjectPropertyFrame, fIdValue)
        m1 = tAnnotations anns . tObjectPropertyExpression True opExpr
            . tClassExpression clExpr $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] RangeSection m2
        newAxioms = ObjectPropertyAxiom opAx : axs

-- FunctionalObjectProperty axiom
tObjectPropertyAxiom opAx@(FunctionalObjectProperty anns opExpr) ms =
   M.insert k (M.insert CharacteristicsSection newAxioms m2) m1
   where
        fIdValue = case opExpr of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr

        k = (ObjectPropertyFrame, fIdValue)
        m1 = tAnnotations anns . tObjectPropertyExpression True opExpr $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] CharacteristicsSection m2
        newAxioms = ObjectPropertyAxiom opAx : axs


-- InverseFunctionalObjectProperty axiom
tObjectPropertyAxiom opAx@(InverseFunctionalObjectProperty anns opExpr) ms =
   M.insert k (M.insert CharacteristicsSection newAxioms m2) m1
   where
        fIdValue = case opExpr of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr

        k = (ObjectPropertyFrame, fIdValue)
        m1 = tAnnotations anns . tObjectPropertyExpression True opExpr $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] CharacteristicsSection m2
        newAxioms = ObjectPropertyAxiom opAx : axs

-- ReflexiveObjectProperty axiom
tObjectPropertyAxiom opAx@(ReflexiveObjectProperty anns opExpr) ms =
   M.insert k (M.insert CharacteristicsSection newAxioms m2) m1
   where
        fIdValue = case opExpr of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr

        k = (ObjectPropertyFrame, fIdValue)
        m1 = tAnnotations anns . tObjectPropertyExpression True opExpr $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] CharacteristicsSection m2
        newAxioms = ObjectPropertyAxiom opAx : axs

-- IrreflexiveObjectProperty axiom
tObjectPropertyAxiom opAx@(IrreflexiveObjectProperty anns opExpr) ms =
   M.insert k (M.insert CharacteristicsSection newAxioms m2) m1
   where
        fIdValue = case opExpr of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr

        k = (ObjectPropertyFrame, fIdValue)
        m1 = tAnnotations anns . tObjectPropertyExpression True opExpr $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] CharacteristicsSection m2
        newAxioms = ObjectPropertyAxiom opAx : axs

-- SymmetricObjectProperty axiom
tObjectPropertyAxiom opAx@(SymmetricObjectProperty anns opExpr) ms =
   M.insert k (M.insert CharacteristicsSection newAxioms m2) m1
   where
        fIdValue = case opExpr of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr

        k = (ObjectPropertyFrame, fIdValue)
        m1 = tAnnotations anns . tObjectPropertyExpression True opExpr $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] CharacteristicsSection m2
        newAxioms = ObjectPropertyAxiom opAx : axs

-- AsymmetricObjectProperty axiom
tObjectPropertyAxiom opAx@(AsymmetricObjectProperty anns opExpr) ms =
   M.insert k (M.insert CharacteristicsSection newAxioms m2) m1
   where
        fIdValue = case opExpr of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr

        k = (ObjectPropertyFrame, fIdValue)
        m1 = tAnnotations anns . tObjectPropertyExpression True opExpr $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] CharacteristicsSection m2
        newAxioms = ObjectPropertyAxiom opAx : axs

-- TransitiveObjectProperty axiom
tObjectPropertyAxiom opAx@(TransitiveObjectProperty anns opExpr) ms =
   M.insert k (M.insert CharacteristicsSection newAxioms m2) m1
   where
        fIdValue = case opExpr of
            ObjectProp iri -> IriId iri
            ObjectInverseOf expr -> ObjInvOfId . obPropExprToIRI $ expr

        k = (ObjectPropertyFrame, fIdValue)
        m1 = tAnnotations anns . tObjectPropertyExpression True opExpr $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] CharacteristicsSection m2
        newAxioms = ObjectPropertyAxiom opAx : axs


-- | transform DataProperty axioms
tDataPropertyAxiom :: DataPropertyAxiom -> MnchstrSntx -> MnchstrSntx
-- SubDataPropertyOf axiom
tDataPropertyAxiom dpAx@(SubDataPropertyOf anns iri1 iri2) ms =
    M.insert k (M.insert SubPropertyOfSection newAxioms m2)  m1
    where
        k = (DataPropertyFrame, IriId iri1)
        m1 = tAnnotations anns . tDataPropertyExpressions [iri1, iri2] $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] SubPropertyOfSection m2
        newAxioms = DataPropertyAxiom dpAx : axs

-- EquivalentDataProperties axiom
tDataPropertyAxiom dpAx@(EquivalentDataProperties anns [iri1, iri2]) ms =
    M.insert k1 (M.insert EquivalentToSection newAxioms1 m1)
    . M.insert k2 (M.insert EquivalentToSection newAxioms2 m2) $ m'
    where
        k1 = (DataPropertyFrame, IriId iri1)
        k2 = (DataPropertyFrame, IriId iri2)
        m' = tAnnotations anns . tDataPropertyExpressions [iri1, iri2] $ ms
        m1 = M.findWithDefault M.empty k1 m'
        m2 = M.findWithDefault M.empty k2 m'
        axioms1 = M.findWithDefault [] EquivalentToSection m1
        axioms2 = M.findWithDefault [] EquivalentToSection m2
        newAx = EquivalentDataProperties anns [iri2, iri1]
        newAxioms1 = DataPropertyAxiom dpAx : axioms1
        newAxioms2 = DataPropertyAxiom newAx : axioms2

tDataPropertyAxiom dpAx@(EquivalentDataProperties anns iris@(_:_:_:_)) ms =
    M.insert k (M.insert EquivalentDataPropertiesSection newAxioms m2) $ m1
    where
        k = (MiscFrame, MiscId)
        m1 = tAnnotations anns . tDataPropertyExpressions iris $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] EquivalentDataPropertiesSection m2
        newAxioms = DataPropertyAxiom dpAx : axs

-- DisjointDataProperties axiom
tDataPropertyAxiom dpAx@(DisjointDataProperties anns [iri1, iri2]) ms =
    M.insert k (M.insert DisjointWithSection newAxioms m2) m1
    where
        k = (DataPropertyFrame, IriId iri1)
        m1 = tAnnotations anns . tDataPropertyExpressions [iri1, iri2] $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] DisjointWithSection m2
        newAxioms = DataPropertyAxiom dpAx : axs

tDataPropertyAxiom dpAx@(DisjointDataProperties anns iris@(_:_:_:_)) ms =
    M.insert k (M.insert DisjointDataPropertiesSection newAxioms m2) m1
    where
        k = (MiscFrame, MiscId)
        m1 = tAnnotations anns . tDataPropertyExpressions iris $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] DisjointDataPropertiesSection m2
        newAxioms = DataPropertyAxiom dpAx : axs

-- DataPropertyDomain axiom
tDataPropertyAxiom dpAx@(DataPropertyDomain anns iri clExpr) ms =
    M.insert k (M.insert DomainSection newAxioms m2) m1
    where
        k = (DataPropertyFrame, IriId iri)
        m1 = tAnnotations anns . tDataPropertyExpression iri
            . tClassExpression clExpr $  ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] DomainSection m2
        newAxioms = DataPropertyAxiom dpAx : axs

-- DataPropertyRange axiom
tDataPropertyAxiom dpAx@(DataPropertyRange anns iri dr) ms =
    M.insert k (M.insert RangeSection newAxioms m2) m1
    where
        k = (DataPropertyFrame, IriId iri)
        m1 = tAnnotations anns . tDataPropertyExpression iri
            . tDataRange dr $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] RangeSection m2
        newAxioms = DataPropertyAxiom dpAx : axs

-- FunctionalDataProperty axiom
tDataPropertyAxiom dpAx@(FunctionalDataProperty anns iri) ms =
    M.insert k (M.insert CharacteristicsSection newAxioms m2) m1
    where
        k = (DataPropertyFrame, IriId iri)
        m1 = tAnnotations anns . tDataPropertyExpression iri $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] CharacteristicsSection m2
        newAxioms = DataPropertyAxiom dpAx : axs

tDataPropertyAxiom _ ms = ms

-- | transform Class axiom
tClassAxiom :: ClassAxiom -> MnchstrSntx -> MnchstrSntx
-- SubClassOf axiom
tClassAxiom clAx@(SubClassOf anns (Expression iri) supClExpr) ms = 
    M.insert k (M.insert SubClassOfSection newAxioms m2) m1
    where
        k = (ClassFrame, IriId iri)
        m1 = tClassExpression supClExpr . tAnnotations anns $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] SubClassOfSection m2
        newAxioms = ClassAxiom clAx : axs

-- EquivalentClasses axiom
tClassAxiom clAx@(EquivalentClasses anns
    [Expression iri1, Expression iri2]) ms =
    M.insert k1 (M.insert EquivalentToSection newAxioms1 m1)
    . M.insert k2 (M.insert EquivalentToSection newAxioms2 m2) $ m'
    where
        m' = tAnnotations anns ms
        k1 = (ClassFrame, IriId iri1)
        k2 = (ClassFrame, IriId iri2)
        m1 = M.findWithDefault M.empty k1 m'
        m2 = M.findWithDefault M.empty k2 m'
        axioms1 = M.findWithDefault [] EquivalentToSection m1
        axioms2 = M.findWithDefault [] EquivalentToSection m2
        newAx = EquivalentClasses anns [Expression iri2, Expression iri1]
        newAxioms1 = ClassAxiom clAx : axioms1
        newAxioms2 = ClassAxiom newAx : axioms2

tClassAxiom clAx@(EquivalentClasses anns [Expression iri, clExpr]) ms =
    M.insert k (M.insert EquivalentToSection newAxioms m1) $ m'
    where
        k = (ClassFrame, IriId iri)
        m' = tAnnotations anns . tClassExpression clExpr $ ms
        m1 = M.findWithDefault M.empty k m'
        axs = M.findWithDefault [] EquivalentToSection m1
        newAxioms = ClassAxiom clAx : axs

tClassAxiom clAx@(EquivalentClasses anns clExprs) ms =
    M.insert k (M.insert EquivalentClassesSection newAxioms m1) $ m'
    where
        k = (MiscFrame, MiscId)
        m' = tAnnotations anns . tClassExpressions clExprs $ ms
        m1 = M.findWithDefault M.empty k m'
        axs = M.findWithDefault [] EquivalentClassesSection m1
        newAxioms = ClassAxiom clAx : axs

-- DisjointClasses axiom
tClassAxiom clAx@(DisjointClasses anns
    [Expression iri1, Expression iri2]) ms =
    M.insert k1 (M.insert DisjointWithSection newAxioms1 m1)
    . M.insert k2 (M.insert DisjointWithSection newAxioms2 m2) $ m'
    where
        k1 = (ClassFrame, IriId iri1)
        k2 = (ClassFrame, IriId iri2)
        m' = tAnnotations anns ms
        m1 = M.findWithDefault M.empty k1 m'
        m2 = M.findWithDefault M.empty k2 m'
        axioms1 = M.findWithDefault [] DisjointWithSection m1
        axioms2 = M.findWithDefault [] DisjointWithSection m2
        newAx = DisjointClasses anns [Expression iri2, Expression iri1]
        newAxioms1 = ClassAxiom clAx : axioms1
        newAxioms2 = ClassAxiom newAx : axioms2

tClassAxiom clAx@(DisjointClasses anns [Expression iri, clExpr]) ms =
    M.insert k (M.insert DisjointWithSection newAxioms m1) $ m'
    where
        k = (ClassFrame, IriId iri)
        m' = tAnnotations anns . tClassExpression clExpr $ ms
        m1 = M.findWithDefault M.empty k m'
        axs = M.findWithDefault [] DisjointWithSection m1
        newAxioms = ClassAxiom clAx : axs

tClassAxiom clAx@(DisjointClasses anns clExprs) ms =
    M.insert k (M.insert DisjointClassesSection newAxioms m1) $ m'
    where
        k = (MiscFrame, MiscId)
        m' = tAnnotations anns . tClassExpressions clExprs $ ms
        m1 = M.findWithDefault M.empty k m'
        axs = M.findWithDefault [] DisjointClassesSection m1
        newAxioms = ClassAxiom clAx : axs

-- DisjointUnion axiom
tClassAxiom clAx@(DisjointUnion anns iri clExprs) ms =
    M.insert k (M.insert DisjointUnionOfSection newAxioms m1) $ m'
    where
        k = (ClassFrame, IriId iri)
        m' = tAnnotations anns . tClassExpressions clExprs $ ms
        m1 = M.findWithDefault M.empty k m'
        axs = M.findWithDefault [] DisjointUnionOfSection m1
        newAxioms = ClassAxiom clAx : axs


tClassAxiom _ ms = ms

-- | transform DatatypeDefinition axiom
tDatatypeDefinition :: Axiom -> MnchstrSntx -> MnchstrSntx
tDatatypeDefinition ax@(DatatypeDefinition anns dtIri dr) ms =
    M.insert k (M.insert EquivalentToSection newAxioms m2) m1
    where
        k = (DatatypeFrame, IriId dtIri)
        m1 = tAnnotations anns . tDatatype dtIri . tDataRange dr $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] EquivalentToSection m2
        newAxioms = ax : axs
        
tDatatypeDefinition _ ms = ms

-- | transform HasKey axiom
tHasKey :: Axiom -> MnchstrSntx -> MnchstrSntx
tHasKey (HasKey anns (Expression iri) opExprs dpExprs) ms =
    M.insert k (M.insert HasKeySection newAxioms m1) $ m'
    where
        k = (ClassFrame, IriId iri)
        opExprs' = S.toList . S.fromList $ opExprs
        dpExprs' = S.toList . S.fromList $ dpExprs
        m' = tAnnotations anns . tObjectPropertyExpressions False opExprs'
            . tDataPropertyExpressions dpExprs' $ ms
        m1 = M.findWithDefault M.empty k m'
        axs = M.findWithDefault [] HasKeySection m1
        newAxioms = (HasKey anns (Expression iri) opExprs' dpExprs') : axs

tHasKey (HasKey anns clExpr opExprs dpExprs) ms =
    tAnnotations anns . tClassExpression clExpr
    . tObjectPropertyExpressions False opExprs
    . tDataPropertyExpressions dpExprs $ ms

tHasKey _  ms = ms

-- | transform Assertion axioms
tAssertion :: Assertion -> MnchstrSntx -> MnchstrSntx
-- SameIndividual axiom
tAssertion ax@(SameIndividual anns [i1, i2]) ms =
    M.insert k1 (M.insert SameAsSection newAxioms1 m1)
    . M.insert k2 (M.insert SameAsSection newAxioms2 m2)
    $ m'
    where
        k1 = (IndividualFrame, IriId i1)
        k2 = (IndividualFrame, IriId i2)
        m' = tAnnotations anns . tIndividuals [i1, i2] $ ms
        m1 = M.findWithDefault M.empty k1 m'
        m2 = M.findWithDefault M.empty k2 m'
        axioms1 = M.findWithDefault [] SameAsSection m1
        axioms2 = M.findWithDefault [] SameAsSection m2
        newAx = SameIndividual anns [i2, i1]
        newAxioms1 = Assertion ax : axioms1
        newAxioms2 = Assertion newAx : axioms2

tAssertion ax@(SameIndividual anns inds@(_:_:_:_)) ms =
    M.insert k (M.insert SameIndividualSection newAxioms m2) m1
    where
        k = (MiscFrame, MiscId)
        m1 = tAnnotations anns . tIndividuals inds $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] SameIndividualSection m2
        newAxioms = Assertion ax : axs 

-- DifferentIndividual axiom
tAssertion ax@(DifferentIndividuals anns [i1, i2]) ms =
    M.insert k1 (M.insert DifferentFromSection newAxioms1 m1)
    . M.insert k2 (M.insert DifferentFromSection newAxioms2 m2)
    $ m'
    where
        k1 = (IndividualFrame, IriId i1)
        k2 = (IndividualFrame, IriId i2)
        m' = tAnnotations anns . tIndividuals [i1, i2] $ ms
        m1 = M.findWithDefault M.empty k1 m'
        m2 = M.findWithDefault M.empty k2 m'
        axioms1 = M.findWithDefault [] DifferentFromSection m1
        axioms2 = M.findWithDefault [] DifferentFromSection m2
        newAx = SameIndividual anns [i2, i1]
        newAxioms1 = Assertion ax : axioms1
        newAxioms2 = Assertion newAx : axioms2

tAssertion ax@(DifferentIndividuals anns inds@(_:_:_:_)) ms =
    M.insert k (M.insert DifferentIndividualsSection newAxioms m2) m1
    where
        k = (MiscFrame, MiscId)
        m1 = tAnnotations anns . tIndividuals inds $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] DifferentIndividualsSection m2
        newAxioms = Assertion ax : axs 

-- ClassAssertion axiom
tAssertion ax@(ClassAssertion anns clExpr iri) ms =
    M.insert k (M.insert TypesSection newAxioms m2) m1
    where
        k = (IndividualFrame, IriId iri)
        m1 = tAnnotations anns . tIndividual iri
            . tClassExpression clExpr $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] TypesSection m2
        newAxioms = Assertion ax : axs 

-- ObjectPropertyAssertion axiom
tAssertion ax@(ObjectPropertyAssertion anns opExpr iri1 iri2) ms =
    M.insert k (M.insert FactsSection newAxioms m2) m1
    where
        k = (IndividualFrame, IriId iri1)
        m1 = tAnnotations anns . tIndividuals [iri1, iri2]
            . tObjectPropertyExpression False opExpr $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] FactsSection m2
        newAxioms = Assertion ax : axs

-- NegativeObjectPropertyAssertion axiom
tAssertion ax@(NegativeObjectPropertyAssertion anns opExpr iri1 iri2) ms =
    M.insert k (M.insert FactsSection newAxioms m2) m1
    where
        k = (IndividualFrame, IriId iri1)
        m1 = tAnnotations anns . tIndividuals [iri1, iri2]
            . tObjectPropertyExpression False opExpr $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] FactsSection m2
        newAxioms = Assertion ax : axs

-- DataPropertyAssertion axiom
tAssertion ax@(DataPropertyAssertion anns dpIri iri lit) ms =
    M.insert k (M.insert FactsSection newAxioms m2) m1
    where
        k = (IndividualFrame, IriId iri)
        m1 = tAnnotations anns . tDataPropertyExpression dpIri
            . tIndividual iri . tLiteral lit $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] FactsSection m2
        newAxioms = Assertion ax : axs

-- NegativeDataPropertyAssertion axiom
tAssertion ax@(NegativeDataPropertyAssertion anns dpIri iri lit) ms =
    M.insert k (M.insert FactsSection newAxioms m2) m1
    where
        k = (IndividualFrame, IriId iri)
        m1 = tAnnotations anns . tDataPropertyExpression dpIri
            . tIndividual iri . tLiteral lit $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] FactsSection m2
        newAxioms = Assertion ax : axs

tAssertion _ ms = ms

-- | transform AnnotationAxiom axioms
tAnnotationAxiom :: AnnotationAxiom -> MnchstrSntx -> MnchstrSntx
-- AnnotationAssertion axiom
tAnnotationAxiom (AnnotationAssertion anns prop subj value) ms = res
    where
        frameIri = case subj of
            AnnSubIri iri -> iri
            AnnSubAnInd iri -> iri

        m' = tAnnotations anns . tAnnotationValue value
            . tAnnotationProperty prop $ ms
        ks = foldr (\f a -> maybe a (const $ (f, IriId frameIri) : a)
            (M.lookup (f, IriId frameIri) m')) [] [minBound..maxBound]
        subTrees = map (\k -> M.findWithDefault M.empty k m') ks
        axiomsList = map (M.findWithDefault [] AnnotationsSection) subTrees
        newAxiom = AnnotationAxiom
            $ (AnnotationAssertion anns prop (AnnSubIri frameIri) value) 
        newAxiomsList = map (newAxiom:) $ axiomsList

        newSubTrees = zipWith (M.insert AnnotationsSection)
            newAxiomsList subTrees

        res = foldl (\m (k, st) -> M.insert k st m) m' $ zip ks newSubTrees

-- SubAnnotationPropertyOf axiom
tAnnotationAxiom ax@(SubAnnotationPropertyOf anns iri1 iri2) ms =
    M.insert k (M.insert SubPropertyOfSection newAxioms m2) m1
    where
        k = (AnnotationPropertyFrame, IriId iri1)
        m1 = tAnnotations anns . tAnnotationProperty iri2 $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] SubPropertyOfSection m2
        newAxioms = AnnotationAxiom ax : axs

-- AnnotationPropertyDomain axiom
tAnnotationAxiom ax@(AnnotationPropertyDomain anns iri1 _) ms =
    M.insert k (M.insert DomainSection newAxioms m2) m1
    where
        k = (AnnotationPropertyFrame, IriId iri1)
        m1 = tAnnotations anns ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] DomainSection m2
        newAxioms = AnnotationAxiom ax : axs

-- AnnotationPropertyRange axiom
tAnnotationAxiom ax@(AnnotationPropertyRange anns iri1 _) ms =
    M.insert k (M.insert RangeSection newAxioms m2) m1
    where
        k = (AnnotationPropertyFrame, IriId iri1)
        m1 = tAnnotations anns ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] RangeSection m2
        newAxioms = AnnotationAxiom ax : axs

tRule :: Rule -> MnchstrSntx -> MnchstrSntx
tRule ax@(DLSafeRule anns body h) ms =
    let k = (RuleFrame, RuleId) 
        m1 = tAnnotations anns . tAtoms body . tAtoms h $ ms
        m2 = M.findWithDefault M.empty k m1
        axs = M.findWithDefault [] RuleSection m2
        newAxioms = Rule ax : axs
    in M.insert k (M.insert RuleSection newAxioms m2) m1
    
tRule _ ms = ms

-- | transform Annotations
tAnnotations :: [Annotation] -> MnchstrSntx -> MnchstrSntx
tAnnotations = flip $ foldr tAnnotation

tAnnotation :: Annotation -> MnchstrSntx -> MnchstrSntx
tAnnotation (Annotation anns annProp annVal) ms =
    M.insert k (M.findWithDefault M.empty k m1) m1
    where
        k = (AnnotationPropertyFrame, IriId annProp)
        m1 = tAnnotations anns . tAnnotationValue annVal $ ms

-- | transform AnnotationProperty
tAnnotationProperty :: IRI -> MnchstrSntx -> MnchstrSntx
tAnnotationProperty iri ms =
    M.insert k (M.findWithDefault M.empty k ms) ms
    where k = (AnnotationPropertyFrame, IriId iri)

-- | transform AnnotationValue
tAnnotationValue :: AnnotationValue -> MnchstrSntx -> MnchstrSntx
tAnnotationValue (AnnAnInd ind) ms = tIndividual ind ms
tAnnotationValue (AnnValue _) ms = ms
tAnnotationValue (AnnValLit lit) ms = tLiteral lit ms

-- | transform AnnotationSubject
tAnnotationSubject :: AnnotationSubject -> MnchstrSntx -> MnchstrSntx
tAnnotationSubject (AnnSubAnInd iri) ms = tIndividual iri ms
tAnnotationSubject _ ms = ms

-- | transform ClassExpression
tClassExpressions :: [ClassExpression] -> MnchstrSntx -> MnchstrSntx
tClassExpressions = flip $ foldr tClassExpression 

tClassExpression :: ClassExpression -> MnchstrSntx -> MnchstrSntx
tClassExpression (Expression iri) ms = 
    M.insert k (M.findWithDefault M.empty k ms) ms
    where k = (ClassFrame, IriId iri)

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
        Cardinality _ _ obPropExpr (Just clExpr) ->
            tObjectPropertyExpression False obPropExpr
            . tClassExpression clExpr $ ms
        Cardinality _ _ obPropExpr Nothing ->
            tObjectPropertyExpression False obPropExpr ms

tClassExpression (DataValuesFrom _ iris dr) ms =
    tDataPropertyExpression (head iris) . tDataRange dr $ ms

tClassExpression (DataHasValue dpExpr lit) ms =
    tDataPropertyExpression dpExpr . tLiteral lit $ ms

tClassExpression (DataCardinality card) ms =
    case card of
        Cardinality _ _ dpExpr (Just dr) ->
            tDataPropertyExpression dpExpr
            . tDataRange dr $ ms
        Cardinality _ _ dpExpr Nothing ->
            tDataPropertyExpression dpExpr ms

-- | transform ObjectPropertyExpression
tObjectPropertyExpressions :: Bool -> [ObjectPropertyExpression]
    -> MnchstrSntx ->  MnchstrSntx
tObjectPropertyExpressions flag = flip $ foldr (tObjectPropertyExpression flag)

tObjectPropertyExpression :: Bool -> ObjectPropertyExpression
    -> MnchstrSntx -> MnchstrSntx
tObjectPropertyExpression _ (ObjectProp iri) ms =
    M.insert k (M.findWithDefault M.empty k ms) ms
    where k = (ObjectPropertyFrame, IriId iri)

tObjectPropertyExpression True (ObjectInverseOf expr) ms =
    M.insert k2 (M.findWithDefault M.empty k2 m1) m1
    where 
        iri = obPropExprToIRI expr
        k1 = (ObjectPropertyFrame, ObjInvOfId iri)
        k2 = (ObjectPropertyFrame, IriId iri)
        m1 = M.insert k1 (M.findWithDefault M.empty k1 ms) ms

tObjectPropertyExpression False (ObjectInverseOf expr) ms =
    M.insert k (M.findWithDefault M.empty k ms) ms
    where k = (ObjectPropertyFrame, IriId . obPropExprToIRI $ expr)

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
    where k = (DatatypeFrame, IriId iri)

-- | transform Literal
tLiteral :: Literal -> MnchstrSntx -> MnchstrSntx
tLiteral (Literal _ t) ms = case t of
    Typed dt -> tDatatype dt ms
    Untyped _ ->  tDatatype plainDatatypeIRI ms

tLiteral (NumberLit _) ms = ms

-- | transform DataPropertyExpression
tDataPropertyExpressions :: [DataPropertyExpression]
    -> MnchstrSntx -> MnchstrSntx
tDataPropertyExpressions = flip $ foldr tDataPropertyExpression

tDataPropertyExpression :: DataPropertyExpression
    -> MnchstrSntx -> MnchstrSntx
tDataPropertyExpression iri ms =
    M.insert k (M.findWithDefault M.empty k ms) ms
    where k = (DataPropertyFrame, IriId iri)

-- | transform Individual
tIndividuals :: [Individual] -> MnchstrSntx -> MnchstrSntx
tIndividuals = flip $ foldr tIndividual

tIndividual :: Individual -> MnchstrSntx -> MnchstrSntx
tIndividual iri ms =
    M.insert k (M.findWithDefault M.empty k ms) ms
    where k = (IndividualFrame, IriId iri)

-- | transform Atoms
tAtoms :: [Atom] -> MnchstrSntx -> MnchstrSntx
tAtoms = flip $ foldr tAtom

tAtom :: Atom -> MnchstrSntx -> MnchstrSntx
tAtom (ClassAtom ce iarg) ms = tClassExpression ce . tIndividualArg iarg $ ms

tAtom (DataRangeAtom dr darg) ms = tDataRange dr . tDataArg darg $ ms

tAtom (ObjectPropertyAtom oe iarg1 iarg2) ms = tObjectPropertyExpression True oe
    . tIndividualArg iarg1 . tIndividualArg iarg2 $ ms

tAtom (DataPropertyAtom dp iarg darg) ms = tDataPropertyExpression dp
    . tIndividualArg iarg . tDataArg darg $ ms

tAtom (BuiltInAtom _ dargs) ms = foldr tDataArg ms dargs

tAtom (SameIndividualAtom iarg1 iarg2) ms = tIndividualArg iarg1
    . tIndividualArg iarg2 $ ms

tAtom (DifferentIndividualsAtom iarg1 iarg2) ms = tIndividualArg iarg1
    . tIndividualArg iarg2 $ ms

tAtom atom _ = error $ "Unexpected Atoms in SWRLRules: " ++ show atom

-- | transform IndividualArg
tIndividualArg :: IndividualArg -> MnchstrSntx -> MnchstrSntx
tIndividualArg iarg ms = case iarg of
    IArg iri -> tIndividual iri ms
    IVar _ -> ms

-- | transform DataArg
tDataArg :: DataArg -> MnchstrSntx -> MnchstrSntx
tDataArg darg ms = case darg of
    DArg lit -> tLiteral lit ms
    DVar _ -> ms
    
------------- main printing part ----------------  

printOntologyDocument :: OntologyDocument -> Doc
printOntologyDocument (OntologyDocument _ prefDecls ont) = 
        (vcat . map printPrefixDeclaration $ M.toList prefDecls)
        $++$ printOntology prefDecls ont

printPrefixDeclaration :: (String, IRI) -> Doc
printPrefixDeclaration (prName, iri) =
    hsep [keyword "Prefix:", text (prName ++ ":"), text . showIRIFull . setAngles True $ iri]

printOntology :: GA.PrefixMap -> Ontology -> Doc
printOntology pds 
    (Ontology mOntIRI mVersionIRI importedDocs annotations axioms') =
        keyword "Ontology:"
        <+> ontIRI
        $++$ impDocs
        $++$ anns
        $++$ axs
    where
        versionIRI = maybe empty (printIRI pds) mVersionIRI
        ontIRI = maybe empty (\x -> printIRI pds x <+> versionIRI) mOntIRI
        impDocs = vcat . map
            (\x -> keyword "Import:" <+> printIRI pds x) $ importedDocs
        anns = printAnnotations pds 0 annotations
        axiomsUnique = S.toList . S.fromList $ axioms'
        ms = tAxioms axiomsUnique emptyMS
        axs = printMS pds ms 

-- | print Manchester Syntax
printMS :: GA.PrefixMap -> MnchstrSntx -> Doc
printMS pds ms = 
    vsep [objectPropertyFrames, dataPropertyFrames, annotationPropertyFrames
        , datatypeFrames, classFrames, individualFrames, miscFrame, rules]
    where
        objectPropertyFrames = printOPFs pds 0 ms
        dataPropertyFrames = printDPFs pds 0 ms
        annotationPropertyFrames = printAPFs pds 0 ms
        datatypeFrames = printDFs pds 0 ms
        classFrames = printCFs pds 0 ms
        individualFrames = printIFs pds 0 ms
        miscFrame = printMF pds 0 ms
        rules = printRules pds 0 ms

-------------------- Print Frames --------------------

-- | print Object Property Frames
printOPFs :: GA.PrefixMap -> Int -> MnchstrSntx -> Doc
printOPFs pds n ms
    | null headers = empty
    | otherwise = foldl ($++$) empty
        . map (\h -> printOPF pds n h $ M.findWithDefault M.empty h ms)
        $ headers
    where
        headers = filter ((== ObjectPropertyFrame) . fst) . M.keys $ ms

-- | print Object Property Frame
printOPF :: GA.PrefixMap -> Int -> FrameId
    -> M.Map FrameSectionType [Axiom] -> Doc
printOPF pds n header body =
    vcat [tabs n <> keyword objectPropertyC <+> hDoc
        , annDoc, subPropOfDoc, subPropChainDoc, eqDoc, disjDoc
        , invDoc, domDoc, rangeDoc, charsDoc]
    where
        hDoc = case snd header of 
                IriId iri -> printIRI pds iri
                ObjInvOfId iri -> keyword inverseS <+> printIRI pds iri
                s -> error $ "Unexpected Frame ID: " ++ show s

        annAxioms = M.findWithDefault [] AnnotationsSection body
        annDoc = annotationAssertionsToDoc pds (n + 1)
            . map unpackAnnotationAxiom $ annAxioms

        subPropOfAxioms = M.findWithDefault [] SubPropertyOfSection body
        subPropOfDoc = opAxiomsToDoc pds (n + 1) SubPropertyOfSection
            . map unpackObjectPropertyAxiom $ subPropOfAxioms
        
        subPropChainAxioms = M.findWithDefault [] SubPropertyChainSection body
        subPropChainDoc = opAxiomsToDoc pds (n + 1) SubPropertyChainSection
            . map unpackObjectPropertyAxiom $ subPropChainAxioms

        eqAxioms = M.findWithDefault [] EquivalentToSection body
        eqDoc = opAxiomsToDoc pds (n + 1) EquivalentToSection
            . map unpackObjectPropertyAxiom $ eqAxioms

        disjAxioms = M.findWithDefault [] DisjointWithSection body
        disjDoc = opAxiomsToDoc pds (n + 1) DisjointWithSection
            . map unpackObjectPropertyAxiom $ disjAxioms

        invAxioms = M.findWithDefault [] InverseOfSection body
        invDoc = opAxiomsToDoc pds (n + 1) InverseOfSection
            . map unpackObjectPropertyAxiom $ invAxioms

        domAxioms = M.findWithDefault [] DomainSection body
        domDoc = opAxiomsToDoc pds (n + 1) DomainSection
            . map unpackObjectPropertyAxiom $ domAxioms

        rangeAxioms = M.findWithDefault [] RangeSection body
        rangeDoc = opAxiomsToDoc pds (n + 1) RangeSection
            . map unpackObjectPropertyAxiom $ rangeAxioms

        charsAxioms = M.findWithDefault [] CharacteristicsSection body
        charsDoc = opAxiomsToDoc pds (n + 1) CharacteristicsSection
            . map unpackObjectPropertyAxiom $ charsAxioms

annotationAssertionsToDoc :: GA.PrefixMap -> Int -> [AnnotationAxiom]
    -> Doc
annotationAssertionsToDoc _ _ [] = empty
annotationAssertionsToDoc pds n axs =
    tabs n <> keyword annotationsC
    $+$
    (vcat . punctuate comma . map (printAnnAssertion pds (n + 1)) $ axs)

opAxiomsToDoc :: GA.PrefixMap -> Int -> FrameSectionType
    -> [ObjectPropertyAxiom] -> Doc
opAxiomsToDoc _ _ _ [] = empty

opAxiomsToDoc pds n SubPropertyOfSection axs =
    tabs n <> keyword subPropertyOfC
    $+$
    (vcat . punctuate comma
        . map (printSubPropOf pds (n + 1)) $ axs)

opAxiomsToDoc pds n SubPropertyChainSection axs =
    vsep
    . map (\d -> tabs n <> keyword subPropertyChainC $+$ d)
    . map (printSubPropChain pds (n + 1))
    $ axs

opAxiomsToDoc pds n EquivalentToSection axs =
    tabs n <> keyword equivalentToC
    $+$
    (vcat . punctuate comma . map (printEqObProp pds (n + 1)) $ axs)

opAxiomsToDoc pds n DisjointWithSection axs =
    tabs n <> keyword disjointWithC
    $+$
    (vcat . punctuate comma . map (printDisjObProp pds (n + 1)) $ axs)

opAxiomsToDoc pds n InverseOfSection axs =
    tabs n <> keyword inverseOfC
    $+$
    (vcat . punctuate comma . map (printInvObProp pds (n + 1)) $ axs)

opAxiomsToDoc pds n DomainSection axs =
    tabs n <> keyword domainC
    $+$
    (vcat . punctuate comma . map (printObPropDom pds (n + 1)) $ axs)

opAxiomsToDoc pds n RangeSection axs =
    tabs n <> keyword rangeC
    $+$
    (vcat . punctuate comma . map (printObPropRange pds (n + 1)) $ axs)

opAxiomsToDoc pds n CharacteristicsSection axs =
    tabs n <> keyword characteristicsC
    $+$
    (vcat . punctuate comma . map (printCharacteristics pds (n + 1)) $ axs)

opAxiomsToDoc  _ _ s _ = error $ "Unexpected Section type in ObjectProperty Frame: " ++ show s

printSubPropOf :: GA.PrefixMap -> Int -> ObjectPropertyAxiom -> Doc
printSubPropOf pds n (SubObjectPropertyOf anns 
    (SubObjPropExpr_obj _) opExpr) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printObjectPropertyExpression pds opExpr

printSubPropOf _ _ ax = error $ "Expected SubObjectPropertyOf, got: " ++ show ax


printSubPropChain :: GA.PrefixMap -> Int -> ObjectPropertyAxiom -> Doc
printSubPropChain pds n (SubObjectPropertyOf anns
    (SubObjPropExpr_exprchain opExprs) _) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> 
    (hcat . punctuate (text " o ")
    . map (printObjectPropertyExpression pds) $ opExprs)
    
printSubPropChain _ _ ax = error $ "Expected SubObjectPropertyOf, got: " ++ show ax

printEqObProp :: GA.PrefixMap -> Int -> ObjectPropertyAxiom -> Doc
printEqObProp pds n (EquivalentObjectProperties anns (_:es)) =
    printAnnotations pds (n + 1) anns
    $+$
    (vcat . punctuate comma
    . map (\e -> tabs (n + 1)
        <> printObjectPropertyExpression pds e) $ es)

printEqObProp _ _ ax = error $ "Expected EquivalentObjectProperties, got: " ++ show ax

printDisjObProp :: GA.PrefixMap -> Int -> ObjectPropertyAxiom -> Doc
printDisjObProp pds n (DisjointObjectProperties anns (_:es)) =
    printAnnotations pds (n + 1) anns
    $+$
    (vcat . punctuate comma
    . map (\e -> tabs (n + 1)
        <> printObjectPropertyExpression pds e) $ es)

printDisjObProp _ _ ax = error $ "Expected DisjointObjectProperties, got: " ++ show ax

printInvObProp :: GA.PrefixMap -> Int -> ObjectPropertyAxiom -> Doc
printInvObProp pds n (InverseObjectProperties anns _ opExpr) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printObjectPropertyExpression pds opExpr
printInvObProp _ _ ax = error $ "Expected InverseObjectProperties, got: " ++ show ax

printObPropDom :: GA.PrefixMap -> Int -> ObjectPropertyAxiom -> Doc
printObPropDom pds n (ObjectPropertyDomain anns _ clExpr) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printClassExpression pds clExpr

printObPropDom _ _ ax = error $ "Expected ObjectPropertyDomain, got: " ++ show ax

printObPropRange :: GA.PrefixMap -> Int -> ObjectPropertyAxiom -> Doc
printObPropRange pds n (ObjectPropertyRange anns _ clExpr) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printClassExpression pds clExpr

printObPropRange _ _ ax = error $ "Expected ObjectPropertyRange, got: " ++ show ax

printCharacteristics :: GA.PrefixMap -> Int -> ObjectPropertyAxiom -> Doc
printCharacteristics pds n (FunctionalObjectProperty anns _) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> keyword functionalS

printCharacteristics pds n (InverseFunctionalObjectProperty anns _) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> keyword inverseFunctionalS

printCharacteristics pds n (ReflexiveObjectProperty anns _) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> keyword reflexiveS

printCharacteristics pds n (IrreflexiveObjectProperty anns _) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> keyword irreflexiveS

printCharacteristics pds n (SymmetricObjectProperty anns _) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> keyword symmetricS

printCharacteristics pds n (AsymmetricObjectProperty anns _) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> keyword asymmetricS

printCharacteristics pds n (TransitiveObjectProperty anns _) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> keyword transitiveS

printCharacteristics  _ _ ax = error $ "Expected ObjectPropertyAxiom, got: " ++ show ax

printAnnAssertion :: GA.PrefixMap -> Int -> AnnotationAxiom -> Doc
printAnnAssertion pds n (AnnotationAssertion anns prop _ value) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printIRI pds prop <+> printAnnotationValue pds value

printAnnAssertion _ _ ax = error $ "Expected AnnotationAxiom, got: " ++ show ax

unpackObjectPropertyAxiom :: Axiom -> ObjectPropertyAxiom
unpackObjectPropertyAxiom (ObjectPropertyAxiom a) = a
unpackObjectPropertyAxiom ax = error $ "Expected ObjectPropertyAxiom, got: " ++ show ax

-- | print Data Property Frames
printDPFs :: GA.PrefixMap -> Int -> MnchstrSntx -> Doc
printDPFs pds n ms 
    | null headers = empty
    | otherwise = foldl ($++$) empty
        . map (\h -> printDPF pds n h $ M.findWithDefault M.empty h ms)
        $ headers
    where
        headers = filter ((== DataPropertyFrame) . fst) . M.keys $ ms

-- | print Data Property Frame
printDPF :: GA.PrefixMap -> Int -> FrameId
    -> M.Map FrameSectionType [Axiom] -> Doc
printDPF pds n header body = 
    vcat [tabs n <> keyword dataPropertyC <+> printIRI pds iri
        , annDoc, subDataPropOfDoc, eqDataPropsDoc, disjDataPropsDoc
        , domDataPropDoc, rangeDataPropDoc, funcDataPropDoc]
    where
        IriId iri = snd header

        annAxioms = M.findWithDefault [] AnnotationsSection body
        annDoc = annotationAssertionsToDoc pds (n + 1)
            . map unpackAnnotationAxiom $ annAxioms

        subDataPropOfAxioms = M.findWithDefault [] SubPropertyOfSection body
        subDataPropOfDoc = dpAxiomsToDoc pds (n + 1) SubPropertyOfSection
            . map unpackDataPropertyAxiom $ subDataPropOfAxioms

        eqDataPropsAxioms = M.findWithDefault [] EquivalentToSection body
        eqDataPropsDoc = dpAxiomsToDoc pds (n + 1) EquivalentToSection
            . map unpackDataPropertyAxiom $ eqDataPropsAxioms

        disjDataPropsAxioms = M.findWithDefault [] DisjointWithSection body
        disjDataPropsDoc = dpAxiomsToDoc pds (n + 1) DisjointWithSection
            . map unpackDataPropertyAxiom $ disjDataPropsAxioms

        domDataPropAxioms = M.findWithDefault [] DomainSection body
        domDataPropDoc = dpAxiomsToDoc pds (n + 1) DomainSection
            . map unpackDataPropertyAxiom $ domDataPropAxioms

        rangeDataPropAxioms = M.findWithDefault [] RangeSection body
        rangeDataPropDoc = dpAxiomsToDoc pds (n + 1) RangeSection
            . map unpackDataPropertyAxiom $ rangeDataPropAxioms

        funcDataPropAxioms = M.findWithDefault [] CharacteristicsSection body
        funcDataPropDoc = dpAxiomsToDoc pds (n + 1) CharacteristicsSection
            . map unpackDataPropertyAxiom $ funcDataPropAxioms

dpAxiomsToDoc :: GA.PrefixMap -> Int -> FrameSectionType
    -> [DataPropertyAxiom] -> Doc
dpAxiomsToDoc _ _ _ [] = empty

dpAxiomsToDoc pds n SubPropertyOfSection axs =
    tabs n <> keyword subPropertyOfC
    $+$
    (vcat . punctuate comma
        . map (printDataPropAxiom pds (n + 1)) $ axs)

dpAxiomsToDoc pds n EquivalentToSection axs =
    tabs n <> keyword equivalentToC
    $+$
    (vcat . punctuate comma
        . map (printDataPropAxiom pds (n + 1)) $ axs)

dpAxiomsToDoc pds n DisjointWithSection axs =
    tabs n <> keyword disjointWithC
    $+$
    (vcat . punctuate comma
        . map (printDataPropAxiom pds (n + 1)) $ axs)

dpAxiomsToDoc pds n DomainSection axs =
    tabs n <> keyword domainC
    $+$
    (vcat . punctuate comma
        . map (printDataPropAxiom pds (n + 1)) $ axs)

dpAxiomsToDoc pds n RangeSection axs =
    tabs n <> keyword rangeC
    $+$
    (vcat . punctuate comma
        . map (printDataPropAxiom pds (n + 1)) $ axs)

dpAxiomsToDoc pds n CharacteristicsSection axs =
    tabs n <> keyword characteristicsC
    $+$
    (vcat . punctuate comma
        . map (printDataPropAxiom pds (n + 1)) $ axs)

dpAxiomsToDoc _ _ s _ = error $ "Unexpected Section type in DataProperty Frame: " ++ show s

printDataPropAxiom :: GA.PrefixMap -> Int -> DataPropertyAxiom -> Doc
printDataPropAxiom pds n (SubDataPropertyOf anns _ iri) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printIRI pds iri

printDataPropAxiom pds n (EquivalentDataProperties anns [_, iri]) = 
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printIRI pds iri

printDataPropAxiom pds n (DisjointDataProperties anns [_, iri]) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printIRI pds iri

printDataPropAxiom pds n (DataPropertyDomain anns _ clExpr) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printClassExpression pds clExpr

printDataPropAxiom pds n (DataPropertyRange anns _ dr) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printDataRange pds dr

printDataPropAxiom pds n (FunctionalDataProperty anns _) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> text functionalS

printDataPropAxiom _ _ ax = error $ "Unexpected DataPropertyAxiom in DataProperty Frame: " ++ show ax
 
unpackDataPropertyAxiom :: Axiom -> DataPropertyAxiom
unpackDataPropertyAxiom (DataPropertyAxiom a) = a
unpackDataPropertyAxiom ax = error $ "Expected DataPropertyAxiom, got: " ++ show ax

-- | print Annotation Property Frames
printAPFs :: GA.PrefixMap -> Int -> MnchstrSntx -> Doc
printAPFs pds n ms
    | null headers = empty
    | otherwise = foldl ($++$) empty
        . map (\h -> printAPF pds n h $ M.findWithDefault M.empty h ms)
        $ headers
    where
        headers = filter ((== AnnotationPropertyFrame) . fst) . M.keys $ ms

-- | print Annotation Property Frame
printAPF :: GA.PrefixMap -> Int -> FrameId
    -> M.Map FrameSectionType [Axiom] -> Doc
printAPF pds n header body = 
    vcat [tabs n <> keyword annotationPropertyC <+> printIRI pds iri
        , annDoc, subPropOfDoc, domainDoc, rangeDoc]
    where
        IriId iri = snd header

        annAxioms = M.findWithDefault [] AnnotationsSection body
        annDoc = annotationAssertionsToDoc pds (n + 1)
            . map unpackAnnotationAxiom $ annAxioms

        subPropOfAxioms = M.findWithDefault [] SubPropertyOfSection body
        subPropOfDoc = afAxiomsToDoc pds (n + 1) SubPropertyOfSection
            . map unpackAnnotationAxiom $ subPropOfAxioms

        domainAxioms = M.findWithDefault [] DomainSection body
        domainDoc = afAxiomsToDoc pds (n + 1) DomainSection
            . map unpackAnnotationAxiom $ domainAxioms

        rangeAxioms = M.findWithDefault [] RangeSection body
        rangeDoc = afAxiomsToDoc pds (n + 1) RangeSection
            . map unpackAnnotationAxiom $ rangeAxioms

afAxiomsToDoc :: GA.PrefixMap -> Int -> FrameSectionType
    -> [AnnotationAxiom] -> Doc
afAxiomsToDoc _ _ _ [] = empty

afAxiomsToDoc pds n frameSectionType axs =
    tabs n <> keyword header
    $+$
    (vcat . punctuate comma
        . map (printAFAxiom pds (n + 1)) $ axs)
    where header = case frameSectionType of
            SubPropertyOfSection -> subPropertyOfC
            DomainSection -> domainC
            RangeSection -> rangeC
            s -> error $ "Unexpected Section type in Annotation Property Frame: " ++ show s


printAFAxiom :: GA.PrefixMap -> Int -> AnnotationAxiom -> Doc
printAFAxiom pds n (SubAnnotationPropertyOf anns _ iri) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printIRI pds iri

printAFAxiom pds n (AnnotationPropertyDomain anns _ iri) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printIRI pds iri

printAFAxiom pds n (AnnotationPropertyRange anns _ iri) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printIRI pds iri

printAFAxiom  _ _ ax = error $ "Unexpected AnnotationAxiom in Annotation Property Frame: " ++ show ax


-- | print Datatype Frames
printDFs :: GA.PrefixMap -> Int -> MnchstrSntx -> Doc
printDFs pds n ms
    | null headers = empty
    | otherwise = foldl ($++$) empty
        . map (\h -> printDF pds n h $ M.findWithDefault M.empty h ms)
        $ headers
    where
        headers = filter ((== DatatypeFrame) . fst) . M.keys $ ms

-- | print Datatype Frame
printDF :: GA.PrefixMap -> Int -> FrameId
    -> M.Map FrameSectionType [Axiom] -> Doc
printDF pds n header body =
    vcat [tabs n <> keyword datatypeC <+> printIRI pds iri
        , annDoc, eqDoc]
    where
        IriId iri = snd header

        annAxioms = M.findWithDefault [] AnnotationsSection body
        annDoc = annotationAssertionsToDoc pds (n + 1)
            . map unpackAnnotationAxiom $ annAxioms

        eqAxioms = M.findWithDefault [] EquivalentToSection body
        eqDoc = dtAxiomsToDoc pds (n + 1) EquivalentToSection eqAxioms

dtAxiomsToDoc :: GA.PrefixMap -> Int -> FrameSectionType
    -> [Axiom] -> Doc
dtAxiomsToDoc _ _ _ [] = empty

dtAxiomsToDoc pds n EquivalentToSection axs =
    tabs n <> keyword equivalentToC
    $+$
    (vcat . punctuate comma
        . map (printDatatypeDefinitionAxiom pds (n + 1)) $ axs)

dtAxiomsToDoc _ _ s _ = error $ "Unexpected Section type in Datateyp Frame: " ++ show s

printDatatypeDefinitionAxiom :: GA.PrefixMap -> Int -> Axiom -> Doc
printDatatypeDefinitionAxiom pds n (DatatypeDefinition anns _ dr) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printDataRange pds dr

printDatatypeDefinitionAxiom _ _ ax = error $ "Unexpected Axiom in Datatype Frame: " ++ show ax

-- | print Class Frames
printCFs :: GA.PrefixMap -> Int -> MnchstrSntx -> Doc
printCFs pds n ms
    | null headers = empty
    | otherwise = foldl ($++$) empty
        . map (\h -> printCF pds n h $ M.findWithDefault M.empty h ms)
        $ headers 
    where
        headers = filter ((== ClassFrame) . fst) . M.keys $ ms

-- | print Class Frame
printCF :: GA.PrefixMap -> Int -> FrameId
    -> M.Map FrameSectionType [Axiom] -> Doc
printCF pds n header body =
    vcat [tabs n <> keyword classC <+> printIRI pds iri
        , annDoc, scoDoc, eqDoc, disjDoc, disjuDoc, haskDoc]
    where
        IriId iri = snd header

        annAxioms = M.findWithDefault [] AnnotationsSection body
        annDoc = annotationAssertionsToDoc pds (n + 1)
            . map unpackAnnotationAxiom $ annAxioms

        scoAxioms = M.findWithDefault [] SubClassOfSection body
        scoDoc = classAxiomsToDoc pds (n + 1) SubClassOfSection scoAxioms

        eqAxioms = M.findWithDefault [] EquivalentToSection body
        eqDoc = classAxiomsToDoc pds (n + 1) EquivalentToSection eqAxioms

        disjAxioms = M.findWithDefault [] DisjointWithSection body
        disjDoc = classAxiomsToDoc pds (n + 1) DisjointWithSection disjAxioms

        disjuAxioms = M.findWithDefault [] DisjointUnionOfSection body
        disjuDoc = classAxiomsToDoc pds (n + 1)
            DisjointUnionOfSection disjuAxioms

        haskAxioms = M.findWithDefault [] HasKeySection body
        haskDoc = hasKeyAxiomsToCFDoc pds (n + 1) haskAxioms


classAxiomsToDoc :: GA.PrefixMap -> Int -> FrameSectionType
    -> [Axiom] -> Doc
classAxiomsToDoc _ _ _ [] = empty

classAxiomsToDoc pds n frameSectionType axs =
    tabs n <> keyword header
    $+$ (printClassAxiomsVer pds (n + 1)
        . map unpackClassAxiom
        $ axs)
    where header = case frameSectionType of
            SubClassOfSection -> subClassOfC
            EquivalentToSection -> equivalentToC
            DisjointWithSection -> disjointWithC
            DisjointUnionOfSection -> disjointUnionOfC
            s -> error $ "Unexpected Section type in Class Frame: " ++ show s

hasKeyAxiomsToCFDoc :: GA.PrefixMap -> Int -> [Axiom] -> Doc
hasKeyAxiomsToCFDoc pds n axs =  
    foldl (\d ax -> printHasKeyAxiom pds n ax $+$ d) empty axs

unpackClassAxiom :: Axiom -> ClassAxiom
unpackClassAxiom (ClassAxiom a) = a
unpackClassAxiom ax = error $ "Expected ClassAxiom, got: " ++ show ax

-- | print HasKey axiom
printHasKeyAxiom :: GA.PrefixMap -> Int -> Axiom -> Doc
printHasKeyAxiom pds n (HasKey anns _ opExprs dpExprs) =
    tabs n <> keyword hasKeyC
    $+$ printAnnotations pds (n + 1) anns
    $+$ resDoc
    where
        resDoc = case (null opExprs, null dpExprs) of
            (True, True) -> empty
            (True, False) -> dpExprsDoc
            (False, True) -> opExprsDoc
            (False, False) -> vcat . punctuate comma $ [opExprsDoc, dpExprsDoc]

        opExprsDoc = vcat . punctuate comma
            . map (\e -> tabs (n + 1) <> 
                        printObjectPropertyExpression pds e) $ opExprs
        dpExprsDoc = vcat . punctuate comma
            . map (\e -> tabs (n + 1) <> printIRI pds e) $ dpExprs

printHasKeyAxiom _ _ ax = error $ "Expected HasKeyAxiom, got: " ++ show ax
         
-- | print ClassAxioms
printClassAxiomsVer :: GA.PrefixMap -> Int -> [ClassAxiom] -> Doc
printClassAxiomsVer pds n =
    vcat . punctuate comma . map (printClassAxiom pds n)

printClassAxiom :: GA.PrefixMap -> Int -> ClassAxiom -> Doc
-- subClassOf axiom
printClassAxiom pds n (SubClassOf anns _ supClExpr) =
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
printClassAxiom pds n (DisjointUnion anns _ clExprs) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printClassExpressionsHor pds clExprs

-- | print Individual Frames
printIFs :: GA.PrefixMap -> Int -> MnchstrSntx -> Doc
printIFs pds n ms
    | null headers = empty
    | otherwise = foldl ($++$) empty
        . map (\h -> printIF pds n h $ M.findWithDefault M.empty h ms)
        $ headers 
    where
        headers = filter ((== IndividualFrame) . fst) . M.keys $ ms

-- | print Individual Frame
printIF :: GA.PrefixMap -> Int -> FrameId
    -> M.Map FrameSectionType [Axiom] -> Doc
printIF pds n header body = 
    vcat [tabs n <> keyword individualC <+> printIRI pds iri
        , annDoc, sameAsDoc, difFromDoc, typesDoc, propAssertionDoc]
    where 
        IriId iri = snd header

        annAxioms = M.findWithDefault [] AnnotationsSection body
        annDoc = annotationAssertionsToDoc pds (n + 1)
            . map unpackAnnotationAxiom $ annAxioms

        sameAsAxioms = M.findWithDefault [] SameAsSection body
        sameAsDoc = iFrameAxiomsToDoc pds (n + 1) SameAsSection $ sameAsAxioms

        difFromAxioms = M.findWithDefault [] DifferentFromSection body
        difFromDoc = iFrameAxiomsToDoc pds (n + 1) DifferentFromSection
            $ difFromAxioms

        typesAxioms = M.findWithDefault [] TypesSection body
        typesDoc = iFrameAxiomsToDoc pds (n + 1) TypesSection $ typesAxioms

        propAssertionAxioms = M.findWithDefault [] FactsSection body
        propAssertionDoc = iFrameAxiomsToDoc pds (n + 1) FactsSection
            $ propAssertionAxioms

iFrameAxiomsToDoc :: GA.PrefixMap -> Int -> FrameSectionType
    -> [Axiom] -> Doc
iFrameAxiomsToDoc _ _ _ [] = empty
iFrameAxiomsToDoc pds n frameSectionType axs = 
    tabs n <> keyword header
    $+$
    (vcat . punctuate comma . map (printIFAssertionAxiom pds (n + 1)) 
        . map (\(Assertion a) -> a) $ axs)
    where header = case frameSectionType of
            SameAsSection -> sameAsC
            DifferentFromSection -> differentFromC
            TypesSection -> typesC
            FactsSection -> factsC
            s -> error $ "Unexpected Section type in Individual Frame: " ++ show s

printIFAssertionAxiom :: GA.PrefixMap -> Int -> Assertion -> Doc
printIFAssertionAxiom pds n (SameIndividual anns [_, ind]) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printIRI pds ind

printIFAssertionAxiom pds n (DifferentIndividuals anns [_, ind]) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printIRI pds ind

printIFAssertionAxiom pds n (ClassAssertion anns clExpr _) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printClassExpression pds clExpr

printIFAssertionAxiom pds n (ObjectPropertyAssertion anns opExpr _ iri2) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printObjectPropertyExpression pds opExpr <+> printIRI pds iri2

printIFAssertionAxiom pds n
    (NegativeObjectPropertyAssertion anns opExpr _ iri2) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> keyword notS
    <+> printObjectPropertyExpression pds opExpr <+> printIRI pds iri2

printIFAssertionAxiom pds n (DataPropertyAssertion anns dpIri _ lit) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <>  printIRI pds dpIri <+> printLiteral pds lit

printIFAssertionAxiom pds n
    (NegativeDataPropertyAssertion anns dpIri _ lit) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> keyword notS <+> printIRI pds dpIri <+> printLiteral pds lit

printIFAssertionAxiom _ _ ax = error $ "Unexpected Assertion in Individual Frame: " ++ show ax

-- | print Misc Frame
printMF :: GA.PrefixMap -> Int -> MnchstrSntx -> Doc
printMF pds n ms
    | M.null mRoot = empty
    | otherwise = 
        vcat [eqClsDoc, disjClsDoc, eqObPropsDoc, disjObPropsDoc
            , eqDataPropsDoc, disjDataPropsDoc, sameIndsDoc, difIndsDoc]
    where
        mRoot = M.findWithDefault M.empty (MiscFrame, MiscId) ms
        eqClsAxioms = M.findWithDefault [] EquivalentClassesSection mRoot
        eqClsDoc = eqClsAxiomsToMFDoc pds n eqClsAxioms

        disjClsAxioms = M.findWithDefault [] DisjointClassesSection mRoot
        disjClsDoc = disjClsAxiomsToMFDoc pds n disjClsAxioms

        eqObPropsAxioms = M.findWithDefault []
            EquivalentObjectPropertiesSection mRoot
        eqObPropsDoc = eqObPropsAxiomsToMFDoc pds n eqObPropsAxioms

        disjObPropsAxioms = M.findWithDefault []
            DisjointObjectPropertiesSection mRoot
        disjObPropsDoc = disjObPropsAxiomsToMFDoc pds n disjObPropsAxioms

        eqDataPropsAxioms = M.findWithDefault [] 
            EquivalentDataPropertiesSection mRoot
        eqDataPropsDoc = eqDataPropsAxiomsToMFDoc pds n eqDataPropsAxioms

        disjDataPropsAxioms = M.findWithDefault []
            DisjointDataPropertiesSection mRoot
        disjDataPropsDoc = disjDataPropsAxiomsToMFDoc pds n disjDataPropsAxioms
        
        sameIndsAxioms = M.findWithDefault [] SameIndividualSection mRoot
        sameIndsDoc = sameIndsAxiomsToMFDoc pds n sameIndsAxioms

        difIndsAxioms = M.findWithDefault [] DifferentIndividualsSection mRoot
        difIndsDoc = difIndsAxiomsToMFDoc pds n difIndsAxioms

eqClsAxiomsToMFDoc :: GA.PrefixMap -> Int -> [Axiom] -> Doc
eqClsAxiomsToMFDoc _ _ [] = empty
eqClsAxiomsToMFDoc pds n axs =
    vsep docsWithHeaders
    where
        classAxioms = map unpackClassAxiom axs
        bodyDocs = map (printClassAxiom pds (n + 1)) classAxioms
        docsWithHeaders = map (\d -> keyword equivalentClassesC $+$ d) bodyDocs

disjClsAxiomsToMFDoc :: GA.PrefixMap -> Int -> [Axiom] -> Doc
disjClsAxiomsToMFDoc _ _[] = empty
disjClsAxiomsToMFDoc pds n axs =
    vsep docsWithHeaders
    where
        classAxioms = map unpackClassAxiom axs
        bodyDocs = map (printClassAxiom pds (n + 1)) classAxioms
        docsWithHeaders = map (\d -> keyword disjointClassesC $+$ d) bodyDocs

eqObPropsAxiomsToMFDoc :: GA.PrefixMap -> Int -> [Axiom] -> Doc
eqObPropsAxiomsToMFDoc _ _[] = empty
eqObPropsAxiomsToMFDoc pds n axs =
    vsep docsWithHeaders
    where 
        opAxioms = map unpackObjectPropertyAxiom axs
        bodyDocs = map (printObPropAxiomMF pds (n + 1)) opAxioms
        docsWithHeaders =
            map (\d -> keyword equivalentPropertiesC $+$ d) bodyDocs

disjObPropsAxiomsToMFDoc :: GA.PrefixMap -> Int -> [Axiom] -> Doc
disjObPropsAxiomsToMFDoc _ _[] = empty
disjObPropsAxiomsToMFDoc pds n axs =
    vsep docsWithHeaders
    where 
        opAxioms = map unpackObjectPropertyAxiom axs
        bodyDocs = map (printObPropAxiomMF pds (n + 1)) opAxioms
        docsWithHeaders =
            map (\d -> keyword disjointPropertiesC $+$ d) bodyDocs

eqDataPropsAxiomsToMFDoc :: GA.PrefixMap -> Int -> [Axiom] -> Doc
eqDataPropsAxiomsToMFDoc _ _ [] = empty
eqDataPropsAxiomsToMFDoc pds n axs = 
    vsep docsWithHeaders
    where
        dpAxioms = map unpackDataPropertyAxiom axs
        bodyDocs = map (printDataPropAxiomMF pds (n + 1)) dpAxioms
        docsWithHeaders = 
            map (\d -> keyword equivalentPropertiesC $+$ d) bodyDocs

disjDataPropsAxiomsToMFDoc :: GA.PrefixMap -> Int -> [Axiom] -> Doc
disjDataPropsAxiomsToMFDoc _ _[] = empty
disjDataPropsAxiomsToMFDoc pds n axs = 
    vsep docsWithHeaders
    where
        dpAxioms = map unpackDataPropertyAxiom axs
        bodyDocs = map (printDataPropAxiomMF pds (n + 1)) dpAxioms
        docsWithHeaders = 
            map (\d -> keyword disjointPropertiesC $+$ d) bodyDocs

sameIndsAxiomsToMFDoc :: GA.PrefixMap -> Int -> [Axiom] -> Doc
sameIndsAxiomsToMFDoc _ _ [] = empty
sameIndsAxiomsToMFDoc pds n axs =
    vsep docsWithHeaders
    where
        unpackedAxioms = map unpackAssertionAxiom axs
        bodyDocs = map (printAssertionAxiomMF pds (n + 1)) unpackedAxioms
        docsWithHeaders = 
            map (\d -> keyword sameIndividualC $+$ d) bodyDocs

difIndsAxiomsToMFDoc :: GA.PrefixMap -> Int -> [Axiom] -> Doc
difIndsAxiomsToMFDoc _ _ [] = empty
difIndsAxiomsToMFDoc pds n axs =
    vsep docsWithHeaders
    where
        unpackedAxioms = map unpackAssertionAxiom axs
        bodyDocs = map (printAssertionAxiomMF pds (n + 1)) unpackedAxioms
        docsWithHeaders = 
            map (\d -> keyword differentIndividualsC $+$ d) bodyDocs

unpackAssertionAxiom :: Axiom -> Assertion
unpackAssertionAxiom (Assertion a) = a
unpackAssertionAxiom ax = error $ "Expected Assertion, got: " ++ show ax

unpackAnnotationAxiom :: Axiom -> AnnotationAxiom
unpackAnnotationAxiom (AnnotationAxiom a) = a
unpackAnnotationAxiom ax = error $ "Expected AnnotationAxiom, got: " ++ show ax

printObPropAxiomMF :: GA.PrefixMap -> Int -> ObjectPropertyAxiom -> Doc
printObPropAxiomMF pds n (EquivalentObjectProperties anns opExprs) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printObjectPropertyExpressionsHor pds opExprs 

printObPropAxiomMF pds n (DisjointObjectProperties anns opExprs) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printObjectPropertyExpressionsHor pds opExprs 

printObPropAxiomMF _ _ ax = error $ "Unexpected ObjectPropertyAxiom in Misc Frame: " ++ show ax

printDataPropAxiomMF :: GA.PrefixMap -> Int -> DataPropertyAxiom -> Doc
printDataPropAxiomMF pds n (EquivalentDataProperties anns dpExprs) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> (hsep . punctuate comma . map (printIRI pds) $ dpExprs)

printDataPropAxiomMF pds n (DisjointDataProperties anns dpExprs) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> (hsep . punctuate comma . map (printIRI pds) $ dpExprs)
    
printDataPropAxiomMF _ _ ax = error $ "Unexpected DataPropertyAxiom in Misc Frame: " ++ show ax

printAssertionAxiomMF :: GA.PrefixMap -> Int -> Assertion -> Doc
printAssertionAxiomMF pds n (SameIndividual anns inds) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> (hsep . punctuate comma . map (printIRI pds) $ inds)

printAssertionAxiomMF pds n (DifferentIndividuals anns inds) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> (hsep . punctuate comma . map (printIRI pds) $ inds)

printAssertionAxiomMF _ _ ax = error $ "Unexpected AssertionAxiom in Misc Frame: " ++ show ax

-- | print Rules
printRules :: GA.PrefixMap -> Int -> MnchstrSntx -> Doc
printRules pds _ ms =
    vcat . map (printRule pds . (\(Rule rule) -> rule))
        . M.findWithDefault [] RuleSection
        . M.findWithDefault M.empty (RuleFrame, RuleId) $ ms

printRule :: GA.PrefixMap -> Rule -> Doc
printRule pds (DLSafeRule anns body h) = 
    text "Rule:" $+$ printAnnotations pds 1 anns 
        $+$ tabs 1 <> printAtoms pds body <+> text " -> " <+> printAtoms pds h
printRule _ rule = text $ "# Unsupported Rule: " ++ show rule

printAtoms :: GA.PrefixMap -> [Atom] -> Doc
printAtoms pds atoms = hcat . punctuate comma . map (printAtom pds) $ atoms

printAtom :: GA.PrefixMap -> Atom -> Doc
printAtom pds (ClassAtom ce iarg) =
    printClassExpression pds ce <> parens (printIndividualArg pds iarg)

printAtom pds (DataRangeAtom dr darg) =
    printDataRange pds dr <> parens (printDataArg pds darg)

printAtom pds (ObjectPropertyAtom oe iarg1 iarg2) =
    printObjectPropertyExpression pds oe
    <> parens (hcat . punctuate comma . map (printIndividualArg pds) $ [iarg1, iarg2])

printAtom pds (DataPropertyAtom dp iarg darg) =
    printIRI pds dp <> (parens $ printIndividualArg pds iarg <> text ", "
        <> printDataArg pds darg)

printAtom pds (BuiltInAtom iri dargs) =  
    printIRI pds iri
    <> parens (hsep . punctuate comma . map (printDataArg pds) $ dargs)

printAtom pds (SameIndividualAtom iarg1 iarg2) =
    text sameAsS
    <> parens (hsep . punctuate comma . map (printIndividualArg pds)
        $ [iarg1, iarg2])

printAtom pds (DifferentIndividualsAtom iarg1 iarg2) =
    text differentFromS
    <> parens (hsep . punctuate comma . map (printIndividualArg pds)
        $ [iarg1, iarg2])

printAtom pds (UnknownUnaryAtom iri uarg) =
    printIRI pds iri
    <> parens (printUnknownArg pds uarg)

printAtom pds (UnknownBinaryAtom iri uarg1 uarg2) =
    printIRI pds iri
    <> parens (hsep . punctuate comma . map (printUnknownArg pds)
        $ [uarg1, uarg2])

printUnknownArg :: GA.PrefixMap -> UnknownArg -> Doc
printUnknownArg pds uarg = case uarg of
    IndividualArg iarg -> printIndividualArg pds iarg
    DataArg darg -> printDataArg pds darg
    Variable var -> text "?" <> printIRI pds var

printIndividualArg :: GA.PrefixMap -> IndividualArg -> Doc
printIndividualArg pds iarg = case iarg of
    IArg iri -> printIRI pds iri
    IVar v -> text "?" <> printIRI pds v

printDataArg :: GA.PrefixMap -> DataArg -> Doc
printDataArg pds darg = case darg of
    DArg iri -> printLiteral pds iri
    DVar v -> text "?" <> printIRI pds v

-- | print Annotations
printAnnotationValue :: GA.PrefixMap -> AnnotationValue -> Doc
printAnnotationValue pds anVal = case anVal of
    AnnAnInd anInd -> printIRI pds anInd
    AnnValue iri -> printIRI pds iri
    AnnValLit lit -> printLiteral pds lit

printAnnotation :: GA.PrefixMap -> Int -> Annotation -> Doc
printAnnotation pds n (Annotation anns ap av) =
    printAnnotations pds (n + 1) anns
    $+$
    (hsep $ [tabs n, docAnnProp, docAnnVal])
    where
        docAnnProp = printIRI pds ap
        docAnnVal = printAnnotationValue pds av

printAnnotations :: GA.PrefixMap -> Int -> Annotations -> Doc
printAnnotations _ _ [] = empty
printAnnotations pds n anns =
    tabs n <> keyword annotationsC
    $+$
    (vcat . punctuate comma . map (printAnnotation pds (n + 1)) $ anns)

-- | print IRI
printIRI :: GA.PrefixMap -> IRI -> Doc
printIRI pds iri
    | isAbbrev iri && prefName `M.member` pds = text (showIRI iri)
    | isAbbrev iri && null prefName = text (showIRIFull iri)
    | otherwise = text (showIRI iri)
  where prefName = prefixName iri


printDataIRI :: GA.PrefixMap -> IRI -> Doc
printDataIRI pds q
    | isDatatypeKey q = text $ showIRI $ setDatatypePrefix q
    | otherwise = printIRI pds q

-- | print Literal
printLiteral :: GA.PrefixMap -> Literal -> Doc
printLiteral pds (Literal lexi ty) =
    case ty of
        Untyped tag -> printUntypedLiteral lexi tag
        Typed iri -> printTypedLiteral pds lexi iri

printLiteral _ (NumberLit f) = text (show f)

printUntypedLiteral :: String -> Maybe String -> Doc
printUntypedLiteral lexi tag = 
    plainText ('"' : escapeString lexi ++ "\"") 
    <> literalTail
    where
        literalTail = case tag of
            Nothing -> empty
            Just tg -> text asP <> text tg

printTypedLiteral :: GA.PrefixMap -> String -> IRI -> Doc 
printTypedLiteral pds lexi iri
    | isAbbrev iri && pn == "xsd" && iFrag == "float" =
        plainText (escapeString lexi) <> text "f"
    | isAbbrev iri && pn == "xsd" && iFrag `elem` ["integer", "decimal"] =
        plainText . escapeString $ lexi
    | otherwise = plainText ('"' : escapeString lexi ++ "\"")
        <> text "^^" <> printDataIRI pds iri
    where
        pn = prefixName iri
        iFrag = iFragment iri

escapeString ::  String -> String
escapeString [] = []
escapeString ('"':s) = '\\' : '"' : escapeString s
escapeString ('\\':s) = '\\' : '\\' : escapeString s
escapeString (c:s) = c : escapeString s 

---------------- | print ObjectPropertyExpression
printObjectPropertyExpressionsVer :: GA.PrefixMap
    -> [ObjectPropertyExpression] -> Doc
printObjectPropertyExpressionsVer pds =
    vcat . punctuate comma . map (printObjectPropertyExpression pds)

printObjectPropertyExpressionsHor :: GA.PrefixMap
    -> [ObjectPropertyExpression] -> Doc
printObjectPropertyExpressionsHor pds =
    hsep . punctuate comma . map (printObjectPropertyExpression pds)

printObjectPropertyExpression :: GA.PrefixMap
    -> ObjectPropertyExpression -> Doc
printObjectPropertyExpression pds obExpr =
    case obExpr of
        ObjectProp ou -> printIRI pds ou
        ObjectInverseOf iopExp -> 
            keyword inverseS
            <+> printObjectPropertyExpression pds iopExp

---------------- | print DataRange
printFV :: GA.PrefixMap -> (ConstrainingFacet, RestrictionValue) -> Doc
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

printDataRange :: GA.PrefixMap -> DataRange -> Doc
printDataRange pds dr = case dr of
    DataType dtype l -> printIRI pds dtype <+>
        if null l then empty else brackets $ sepByCommas $ map (printFV pds) l
    DataComplementOf drange -> keyword notS <+> printDataRange pds drange
    DataOneOf constList ->
        specBraces . fsep . punctuate comma . map (printLiteral pds) $ constList
    DataJunction ty drlist -> let
      k = case ty of
          UnionOf -> orS
          IntersectionOf -> andS
      in fsep $ prepPunctuate (keyword k <> space)
            $ map (printDataRange pds) drlist

---------------- | print ClassExpression
printClassExpressionsHor :: GA.PrefixMap -> [ClassExpression] -> Doc
printClassExpressionsHor pds =
    hsep . punctuate comma . map (printClassExpression pds)

printClassExpressionsVer :: GA.PrefixMap -> [ClassExpression] -> Doc
printClassExpressionsVer pds =
    vcat . punctuate comma . map (printClassExpression pds)

printClassExpression :: GA.PrefixMap -> ClassExpression -> Doc
printClassExpression pds expr = case expr of 
    Expression ocUri -> printIRI pds ocUri
    ObjectJunction ty ds -> let
        k = case ty of
            UnionOf -> orS
            IntersectionOf -> andS
        in fsep . prepPunctuate (keyword k <> space)
                . map (printPrimary pds) $ ds
    ObjectComplementOf d -> keyword notS <+> printPrimary pds d
    ObjectOneOf indUriList ->
        specBraces . fsep . punctuate comma . map (printIRI pds) $ indUriList
    ObjectValuesFrom ty opExp d ->
        printObjectPropertyExpression pds opExp
        <+> quantifierType ty
        <+> printPrimary pds d
    ObjectHasSelf opExp ->
        printObjectPropertyExpression pds opExp <+> keyword selfS
    ObjectHasValue opExp indUri ->
        printObjectPropertyExpression pds opExp 
        <+> keyword valueS <+> printIRI pds indUri
    ObjectCardinality (Cardinality ty card opExp maybeDesc) ->
        printObjectPropertyExpression pds opExp <+> cardinalityType ty
        <+> text (show card)
        <+> maybe (keyword "owl:Thing") (printPrimary pds) maybeDesc
    DataValuesFrom ty dpExp dRange ->
        printIRI pds (head dpExp) <+> quantifierType ty
        <+> printDataRange pds dRange
    DataHasValue dpExp cons ->
        printIRI pds dpExp <+> keyword valueS <+> printLiteral pds cons
    DataCardinality (Cardinality ty card dpExp maybeRange) ->
        printIRI pds dpExp <+> cardinalityType ty 
        <+> text (show card)
        <+> maybe empty (printDataRange pds) maybeRange

printPrimary :: GA.PrefixMap -> ClassExpression -> Doc
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

