module OWL2.PrintOWL2AS where

import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Keywords
import Common.IRI

import OWL2.AS
import OWL2.Symbols
import OWL2.Keywords
import OWL2.ColonKeywords
import OWL2.OWL2ASKeywords

import Data.List

-- | auxiliary parens function
sParens d = parens (space <> d <> space)

-- | print IRI

instance Pretty IRI where
    pretty iri
        | ((hasFullIRI iri || prefixName iri `elem`
                                ["", "xsd", "rdf", "rdfs", "owl"])
            && isPredefPropOrClass iri)
            || isDatatypeKey iri = keyword $ getPredefName iri
        | otherwise = text $ showIRI iri

printDataIRI :: IRI -> Doc
printDataIRI q = if isDatatypeKey q then text $ showIRI $ setDatatypePrefix q
    else pretty q

-- instance Pretty LexicalForm where
--     pretty = doubleQuotes . text

-- instance Pretty LanguageTag where
--     pretty = text

-- | print Literal

instance Pretty Literal where
    pretty lit = case lit of
        Literal lexi ty -> let
          escapeDQ c s = case s of
            "" -> ""
            h : t -> case h of
              '\\' -> h : escapeDQ (c + 1 :: Int) t
              _ | odd c || h /= '"' -> h : escapeDQ 0 t
              _ -> '\\' : h : escapeDQ 0 t
          in plainText ('"' : escapeDQ 0 lexi ++ "\"") <> case ty of
            Typed u -> keyword cTypeS <> printDataIRI u
            Untyped tag -> case tag of
              Nothing -> empty
              Just tag2 -> text asP <> text tag2
        NumberLit f -> text (show f)


-- | print Individual
instance Pretty AnonymousIndividual where
    pretty = doubleQuotes . text

instance Pretty Individual where
    pretty ind = case ind of
        NamedIndividual_ ni -> pretty ni
        AnonymousIndividual ai -> pretty ai

-- | print PropertyExpression

instance Pretty ObjectPropertyExpression where
    pretty = printObjPropExp

printObjPropExp :: ObjectPropertyExpression -> Doc
printObjPropExp obExp = case obExp of
    ObjectProp ou -> pretty ou
    ObjectInverseOf iopExp -> keyword objectInverseOfS 
        <> sParens (printObjPropExp iopExp)

-- | print Entity

instance Pretty Entity where
    pretty (Entity _ ty e) = keyword entityTypeS <> sParens (pretty e)
    where entityTypeS = case ty of
        Datatype -> "Datatype"
        Class -> "Class"
        ObjectProperty -> "ObjectProperty"
        DataProperty -> "DataProperty"
        AnnotationProperty -> "AnnotationProperty"
        NamedIndividual -> "NamedIndividual"

-- | print DataRanges

instance Pretty DataRange where
    pretty dr = case dr of
        DataType dt fvs -> printDataRestriction dt fvs
        DataJunction jt drs -> printDataJunction jt drs
        DataComplementOf dr -> printDataComplementOf dr
        DataOneOf lits -> printDataOneOf lits

printDataRestriction :: Datatype -> [(ConstrainingFacet, RestrictionValue)]
    -> Doc
printDataRestriction dt fvs
    | null fvs = pretty dt
    | otherwise = keyword datatypeRestrictionS
        <> sParens (hsep . concat $ [[pretty dt], map pretty fvsUnwrapped])
    where fvsUnwrapped = concat [[f, v] | (f, v) <- fvs]

printDataJunction :: JunctionType -> [DataRange] -> Doc
printDataJunction jt drs = junctionKeyword <> sParens (hsep . map pretty $ drs)
    where junctionKeyword = case jt of 
        UnionOf -> keyword dataUnionOfS
        IntersectionOf -> keyword dataIntersectionOfS

printDataComplementOf :: DataRange -> Doc
printDataComplementOf dr = keyword dataComplementOfS <> sParens (pretty dr)

printDataOneOf :: [Literal] -> Doc
printDataOneOf lits = keyword dataOneOfS <> sParens (hsep . map pretty $ lits)

-- | print ClassExpressions

instance Pretty ClassExpression where
    pretty clExpr = case clExpr of
        Expression cl -> pretty cl
        ObjectJunction jt clExprs -> printObjectJunction jt clExprs
        ObjectComplementOf clexpr -> printObjectComplementOf clexpr
        ObjectOneOf inds -> printObjectOneOf inds
        ObjectValuesFrom qt obPropExpr clexpr ->
            printObjectValuesFrom qt obPropExpr clexpr
        ObjectHasValue objPropExpr ind ->
            printObjectHasValue objPropExpr ind
        ObjectHasSelf objPropExpr -> printObjectHasSelf objPropExpr
        ObjectCardinality card -> printObjectCardinality card
        DataValuesFrom qt dPropExprs dr ->
            printDataValuesFrom qt dPropExprs dr
        DataHasValue dPropExpr lit -> printDataHasValue dPropExpr lit
        DataCardinality card -> printDataCardinality card

printObjectJunction :: JunctionType -> [ClassExpression] -> Doc
printObjectJunction jt clExprs = junctionKeyword
    <> sParens (hsep . map pretty $ clExprs)
    where junctionKeyword = case jt of
        UnionOf -> keyword objectUnionOfS
        IntersectionOf -> keyword objectIntersectionOfS

printObjectComplementOf :: ClassExpression -> Doc
printObjectComplementOf clexpr = keyword objectComplementOfS
    <> sParens (pretty clexpr)

printObjectOneOf :: [Individual] -> Doc
printObjectOneOf inds = keyword objectOneOfS
    <> sParens (hsep . map pretty $ inds)

printObjectValuesFrom :: QuantifierType -> ObjectPropertyExpression
    -> ClassExpression -> Doc
printObjectValuesFrom qt obPropExpr clexpr =
    quantifierKeyword <> sParens (hsep . map pretty $ [obPropExpr, clexpr])
    where
        quantifierKeyword = case qt of
            AllValuesFrom -> keyword objectAllValuesFromS
            SomeValuesFrom -> keyword objectSomeValuesFromS

printObjectHasValue :: ObjectPropertyExpression -> Individual -> Doc
printObjectHasValue objPropExpr ind = keyword objectHasValueS
    <> sParens (hsep . map pretty $ [objPropExpr, ind])

printObjectHasSelf :: ObjectPropertyExpression -> Doc
printObjectHasSelf objPropExpr = keyword objectHasSelfS
    <> sParens (pretty objPropExpr)

printObjectCardinality :: Cardinality ObjectPropertyExpression ClassExpression
    -> Doc
printObjectCardinality card =
    cardinalityKeyword <> sParens (hsep $
        [text [show n], pretty objPropExpr, pretty clExpr])
    where
        (Cardinality cardType n objPropExpr mClExpr) = card
        cardinalityKeyword = case cardType of
            MaxCardinality -> keyword objectMaxCardinalityS
            MinCardinality -> keyword objectMinCardinalityS
            ExactCardinality -> keyword objectExactCardinalityS
        clExpr = case mClExpr of
            Nothing -> empty
            Just clexpr -> clexpr

printDataValuesFrom :: QuantifierType -> [DataPropertyExpression] -> DataRange
    -> Doc
printDataValuesFrom qt dPropExprs dr =
    quantifierKeyword <> sParens (hsep . concat $
        [map pretty dPropExprs, [pretty dr]])
    where
        quantifierKeyword = case qt of
            AllValuesFrom -> keyword dataAllValuesFromS
            SomeValuesFrom -> keyword dataSomeValuesFromS

printDataCardinality :: Cardinality DataPropertyExpression DataRange
printDataCardinality card = cardinalityKeyword <> sParens (hsep $
        [text [show n], pretty dataPropExpr, pretty dr])
    where
        (Cardinality cardType n dataPropExpr mDr) = card
        cardinalityKeyword = case cardType of
            MaxCardinality -> keyword dataMaxCardinalityS
            MinCardinality -> keyword dataMinCardinalityS
            ExactCardinality -> keyword dataExactCardinalityS
        dr = case mDr of
            Nothing -> empty
            Just drange -> drange

printDataHasValue :: DataPropertyExpression -> Literal -> Doc
printDataHasValue dPropExpr lit = 
    keyword dataHasValueS <> sParens(hsep . map pretty $ [dPropExpr, lit])

-- | print Annotations

instance Pretty AnnotationValue where
    pretty anVal = case anVal of
        AnnAnInd anInd -> pretty anInd
        AnnValue iri -> pretty iri
        AnnValLit lit -> pretty lit

instance Pretty Annotation where
    pretty (Annotation ans anProp anVal) =
        keyword annotationS <> sParens (hsep . concat $
            [map pretty ans, [pretty anProp, pretty anVal]])

instance Pretty OntologyAnnotations where
    pretty = map pretty

instance Pretty AnnotationSubject where
    pretty annSub = case annSub of
        AnnSubIri iri -> pretty iri
        AnnSubAnInd ind -> pretty ind

instance Pretty AnnotationAxiom where
    pretty annAx = case annAx of 
        AnnotationAssertion axAnns annProp annSub annVal ->
            printAnnotationAssertion axAnns annProp annSub annVal
        SubAnnotationPropertyOf axAnns subAnnProp supAnnProp ->
            printSubAnnotationPropertyOf axAnns subAnnProp supAnnProp
        AnnotationPropertyDomain axAnns annProp iri ->
            printAnnotationPropertyDomain axAnns annProp iri
        AnnotationPropertyRange axAnns annProp iri ->
            printAnnotationPropertyRange axAnns annProp iri

printAnnotationAssertion :: AxiomAnnotations -> AnnotationProperty
    -> AnnotationSubject -> AnnotationValue -> Doc
printAnnotationAssertion axAnns annProp annSub annVal = 
    keyword annotationAssertionS <> sParens (hsep . concat . map (map pretty) $
        [axAnns, [annProp, annSub, annVal]])

printSubAnnotationPropertyOf :: AxiomAnnotations -> SubAnnotationProperty
    -> SuperAnnotationProperty -> Doc
printSubAnnotationPropertyOf axAnns subAnnProp supAnnProp =
    keyword subAnnotationPropertyOfS
    <> sParens (hsep . concat . map (map pretty ) $
        [axAnns, [subAnnProp, supAnnProp]])

printAnnotationPropertyDomain :: AxiomAnnotations -> AnnotationProperty
    -> IRI -> Doc
printAnnotationPropertyDomain axAnns annProp iri =
    keyword annotationPropertyDomainS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, [annProp, iri]])

printAnnotationPropertyRange :: AxiomAnnotations -> AnnotationProperty
    -> IRI -> Doc
printAnnotationPropertyRange axAnns annProp iri =
    keyword annotationPropertyRangeS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, [annProp, iri]])

-- | print Axioms

instance Pretty Axiom where
    pretty axiom = case axiom of
        ClassAxiom ax -> pretty ax
        ObjectPropertyAxiom ax -> pretty ax
        DataPropertyAxiom ax -> pretty ax
        DatatypeDefinition axAnns dt dr 
            -> printDatatypeDefinition axAnns dt dr
        HasKey axAnns clExpr objPropExprs dataPropExprs
            -> printHasKey axAnss clExpr objPropExprs dataPropExprs
        Assertion ax -> pretty ax
        AnnotationAxiom ax -> pretty ax

-- | print ClassAxiom

instance Pretty ClassAxiom where
    pretty ca = case ca of 
        SubClassOf axAnns subClExpr supClExpr ->
            printSubClassOf axAnns subClExpr supClExpr
        EquivalentClasses axAnns clExprs ->
            printEquivalentClasses axAnns clExprs
        DisjointClasses axAnns clExprs -> printDisjointClasses axAnns clExprs
        DisjointUnion axAnns cl disjClExprs ->
            printDisjointUnion axAnns cl disjClExprs

printSubClassOf :: AxiomAnnotations -> SubClassExpression
    -> SuperClassExpression -> Doc
printSubClassOf axAnns subClExpr supClExpr =
    keyword subClassOfS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, [subClExpr, supClExpr]])

printEquivalentClasses :: AxiomAnnotations -> [ClassExpression] -> Doc
printEquivalentClasses axAns clExprs =
    keyword equivalentClassesS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, clExprs]])

printDisjointClasses :: AxiomAnnotations -> [ClassExpression] -> Doc
printDisjointClasses axAns clExprs =
    keyword disjointClassesS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, clExprs]])

printDisjointUnion ::AxiomAnnotations -> Class -> DisjointClassExpression 
    -> Doc
printDisjointUnion axAnns cl disjClExprs = 
    keyword disjointUnionS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, [cl], disjClExprs])

-- | print SubObjectProperyExpression
instance Pretty SubObjectPropertyExpression where
    pretty (SubObjPropExpr_obj objPropExpr) = pretty objPropExpr
    pretty (SubObjPropExpr_exprchain propExprChain) = 
        keyword objectPropertyChainS
        <> sParens (hsep . map pretty $ propExprChain)

-- | print ObjectPropertyAxiom
instance Pretty ObjectPropertyAxiom where
    pretty ax = case ax of
        SubObjectPropertyOf axAnns subObjPropExpr supObjPropExpr
            -> printSubObjectPropertyOf axAnns subObjePropExpr supObjPropExpr
        EquivalentObjectProperties axAnns objPropExprs
            -> printEquivalentObjectProperties axAnns objPropExprs
        DisjointObjectProperties axAnns objPropExprs
            -> printDisjointObjectProperties axAnns objPropExprs
        InverseObjectProperties axAnns objPropExpr1 objPropExpr2
            -> printInverseObjectProperties axAnns objPropExpr1 objPropExpr2
        ObjectPropertyDomain axAnns objPropExpr clExpr
            -> printObjectPropertyDomain axAnns objPropExpr clExpr
        ObjectPropertyRange axAnns objPropExpr clExpr
            -> printObjectPropertyRange axAnns objPropExpr clExpr
        FunctionalObjectProperty axAnns objPropExpr
            -> printFunctionalObjectProperty axAnns objPropExpr
        InverseFunctionalObjectProperty axAnns objPropExpr
            -> printInverseFunctionalObjectProperty axAnns objPropExpr
        ReflexiveObjectProperty  axAnns objPropExpr
            -> printReflexiveObjectProperty  axAnns objPropExpr
        SymmetricObjectProperty  axAnns objPropExpr
            -> printISymmetricObjectProperty  axAnns objPropExpr
        AsymmetricObjectProperty axAnns objPropExpr
            -> printAsymmetricObjectProperty axAnns objPropExpr
        TransitiveObjectProperty axAnns objPropExpr
            -> printTransitiveObjectProperty axAnns objPropExpr

printSubObjectPropertyOf :: AxiomAnnotations -> SubObjectPropertyExpression
    -> SuperObjectPropertyExpression -> Doc
printSubObjectPropertyOf axAnns subObjPropExpr supObjPropExpr =
    keyword subObjectPropertyOfS
    <> sParens (hsep . concat . map (map pretty) $ 
        [axAnns, [subObjPropExpr, supObjPropExpr]])

printEquivalentObjectProperties :: AxiomAnnotations
    -> [ObjectPropertyExpression] -> Doc
printEquivalentObjectProperties axAnns objPropExprs =
    keyword equivalentObjectPropertiesS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnss, objPropExprs])

printDisjointObjectProperties :: AxiomAnnotations
    -> [ObjectPropertyExpression] -> Doc
printDisjointObjectProperties axAnns objPropExprs =
    keyword disjointObjectPropertiesS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, objPropExprs])

printInverseObjectProperties :: AxiomAnnotations -> ObjectPropertyExpression
    -> ObjectPropertyExpression -> Doc
printInverseObjectProperties axAnns objPropExpr1 objPropExpr2 =
    keyword inverseObjectPropertiesS
    <> sParens (hsep . concat . map (map pretty) $ 
        [axAnns, [objPropExpr1, objPropExpr2]])

printObjectPropertyDomain :: AxiomAnnotations -> ObjectPropertyExpression
    -> ClassExpression -> Doc
printObjectPropertyDomain axAnns objPropExpr clExpr =
    keyword objectPropertyDomainS
    <> sParens (hsep . concat . map (map pretty) $ 
        [axAnns, [objPropExpr, clExpr]])

printObjectPropertyRange :: AxiomAnnotations -> ObjectPropertyExpression
    -> ClassExpression -> Doc
printObjectPropertyRange axAnns objPropExpr clExpr = 
    keyword objectPropertyRangeS
    <> sParens (hsep . concat . map (map pretty) $ 
        [axAnns, [objPropExpr, clExpr]])

printFunctionalObjectProperty :: AxiomAnnotations -> ObjectPropertyExpression
    -> Doc
printFunctionalObjectProperty axAnns objPropExpr =
    keyword functionalObjectPropertyS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, [objPropExpr]])

printInverseFunctionalObjectProperty :: AxiomAnnotations -> ObjectPropertyExpression
    -> Doc
printInverseFunctionalObjectProperty axAnns objPropExpr =
    keyword inverseFunctionalObjectPropertyS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, [objPropExpr]])

printReflexiveObjectProperty :: AxiomAnnotations -> ObjectPropertyExpression
    -> Doc
printReflexiveObjectProperty axAnns objPropExpr =
    keyword reflexiveObjectPropertyS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, [objPropExpr]])

printSymmetricObjectProperty :: AxiomAnnotations -> ObjectPropertyExpression
    -> Doc
printSymmetricObjectProperty axAnns objPropExpr =
    keyword symmetricObjectPropertyS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, [objPropExpr]])

printAsymmetricObjectProperty :: AxiomAnnotations -> ObjectPropertyExpression
    -> Doc
printAsymmetricObjectProperty axAnns objPropExpr =
    keyword asymmetricObjectPropertyS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, [objPropExpr]])

printTransitiveObjectProperty :: AxiomAnnotations -> ObjectPropertyExpression
    -> Doc
printTransitiveObjectProperty axAnns objPropExpr =
    keyword transitiveObjectPropertyS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, [objPropExpr]])

-- | print DataPropertyAxiom
instance Pretty DataPropertyAxiom where
    pretty ax = case ax of
        SubDataPropertyOf axAnns subDataPropExpr supDataPropExpr
            -> printSubDataPropertyOf
        EquivalentDataProperties axAnns dataPropExprs
            -> printEquivalentDataProperties axAnns dataPropExprs
        DisjointDataProperties axAnns dataPropExprs
            -> printDisjointDataProperties axAnns dataPropExprs
        DataPropertyDomain axAnns dataPropExpr clExpr
            -> printDataPropertyDomain axAnns dataPropExpr clExpr
        DataPropertyRange axAnns dataPropExpr dr
            -> printDataPropertyRange  axAnns dataPropExpr dr
        FunctionalDataProperty axAnns dataPropExpr
            -> printFunctionalDataProperty axAnns dataPropExpr

printSubDataPropertyOf :: AxiomAnnotations -> SubDataPropertyExpression
    -> SuperDataPropertyExpression -> Doc
printSubDataPropertyOf axAnns subDataPropExpr supDataPropExpr = 
    keyword subDataPropertyOfS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, [subDataPropExpr, supDataPropExpr]])

printEquivalentDataProperties :: AxiomAnnotations -> [DataPropertyExpression]
    -> Doc
printEquivalentDataProperties axAnns dataPropExprs =
    keyword equivalentDataPropertiesS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, dataPropExprs])

printDisjointDataProperties :: AxiomAnnotations -> [DataPropertyExpression]
    -> Doc
printDisjointDataProperties axAnns dataPropExprs =
    keyword disjointDataPropertiesS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, dataPropExprs])

printDataPropertyDomain :: AxiomAnnotations -> DataPropertyExpression
    -> ClassExpression -> Doc
printDataPropertyDomain axAnns dataPropExpr clExpr =
    keyword dataPropertyDomainS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, [datapropExpr, clExpr]])

printDataPropertyRange  :: AxiomAnnotations -> DataPropertyExpression 
    -> DataRange -> Doc
printDataPropertyRange  axAnns dataPropExpr dr =
    keyword dataPropertyRangeS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, [dataPropExpr, dr]])

printFunctionalDataProperty :: AxiomAnnotations -> DataPropertyExpression -> Doc
printFunctionalDataProperty axAnns dataPropExpr =
    keyword functionalDataPropertyS
    <> sParens (hsep . concat . map (map pretty) $ 
        [axAnns, [dataPropExpr]])

-- | print DatatypeDefinition axiom

printDatatypeDefinition :: AxiomAnnotations -> Datatpye -> DataRange -> Doc
printDatatypeDefinition axAnns dt dr =
    keyword datatypeDefinitionS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, [dt, dr]])

-- | print HasKey axiom

printHasKey :: AxiomAnnotations -> ClassExpression -> ObjectPropertyExpression
    -> DataPropertyExpression -> Doc
printHasKey axAnss clExpr objPropExprs dataPropExprs =
    keyword hasKeyS
    <> sParens (hsep [map pretty axAnns, pretty clExpr,
        objPropExprsDoc, dataPropExprsDoc])
    where
        objPropExprsDoc = sParens . hsep . map pretty $ objPropExprs
        dataPropExprsDoc = sParens . hsep . map pretty $ dataPropExprs

-- | print Assertion axiom
instance Pretty Assertion where
    pretty ax = case ax of
        SameIndividual axAnns inds -> printSameIndividual axAnns inds
        DifferentIndividuals axAnns indx
            -> printDifferentIndividuals axAnns inds
        ClassAssertion axAnns clExpr ind
            -> printClassAssertion axAnns clExpr ind
        ObjectPropertyAssertion axAnns objPropExpr srcInd targInd
            -> printObjectPropertyAssertion axAnns objPropExpr srcInd targInd
        NegativeObjectPropertyAssertion axAnns objPropExpr srcInd targInd
            -> printNegativeObjectPropertyAssertion axAnns objPropExpr srcInd
                targInd
        DataPropertyAssertion axAnns dataPropExpr srcInd targInd
            -> printDataPropertyAssertion axAnns dataPropExpr srcInd targInd
        NegativeDataPropertyAssertion axAnns dataPropExpr srcInd targInd
            -> printNegativeDataPropertyAssertion axAnns dataPropExpr srcInd
                targInd

printSameIndividual :: AxiomAnnotations -> [Individual] -> Doc
printSameIndividual axAnns inds =
    keyword sameIndividualS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, inds])

printDifferentIndividuals :: AxiomAnnotations -> [Individual] -> Doc
printDifferentIndividuals axAnns inds =
    keyword differentIndividualsS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, inds])

printClassAssertion :: AxiomAnnotations -> ClassExpression -> Individual -> Doc
printClassAssertion axAnns clExpr ind =
    keyword classAssertionS
    <> eParens (hsep . concat . map (map pretty) $
        [axAnns, [clExpr, ind]])

printObjectPropertyAssertion :: AxiomAnnotations -> ObjectPropertyExpression
    -> SourceIndividual -> TargetIndividual -> Doc
printObjectPropertyAssertion axAnns objPropExpr srcInd targInd =
    keyword objectPropertyAssertionS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, [objPropExpr, srcInd, targInd]])

printNegativeObjectPropertyAssertion :: AxiomAnnotations
    -> ObjectPropertyExpression -> SourceIndividual -> TargetIndividual -> Doc
printNegativeObjectPropertyAssertion axAnns objPropExpr srcInd targInd =
    keyword objectPropertyAssertionS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, [objPropExpr, srcInd, targInd]])

printDataPropertyAssertion :: AxiomAnnotations -> DataPropertyExpression
    -> SourceIndividual -> TargetIndividual -> Doc
printDataPropertyAssertion axAnns dataPropExpr srcInd targInd =
    keyword dataPropertyAssertionS
    <> sParens (hsep . concat . map (map pretty) $
      [axAnns, [dataPropExpr, srcInd, targInd]])

printNegativeDataPropertyAssertion :: AxiomAnnotations -> DataPropertyExpression
    -> SourceIndividual -> TargetIndividual -> Doc
printNegativeDataPropertyAssertion axAnns dataPropExpr srcInd targInd =
    keyword negativeDataPropertyAssertionS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, [dataPropExpr, srcInd, targInd]])

-- | print AnnotationAxiom
instance Pretty AnnotationAxiom where
    pretty ax = case ax of 
        AnnotationAssertion axAnns annProp annSub annValue
            -> printAnnotationAssertion axAnns annProp annSub annValue
        SubAnnotationPropertyOf axAnns subAnnProp supAnnProp
            -> printSubAnnotationPropertyOf axAnns subAnnProp supAnnProp
        AnnotationPropertyDomain axAnns annProp iri
            -> printAnnotationPropertyDomain axAnns annProp iri
        AnnotationPropertyRange axAnns annProp iri
            -> printAnnotationPropertyRange axAnns annProp iri

printAnnotationAssertion :: AxiomAnnotations -> AnnotationProperty
    -> AnnotationSubject ->  AnnotationValue -> Doc
printAnnotationAssertion axAnns annProp annSub annValue =
    keyword annotationAssertionS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, [annProp, annSub, annValue]])

printSubAnnotationPropertyOf :: AxiomAnnotations -> SubAnnotationProperty
    -> SuperAnnotationProperty -> Doc
printSubAnnotationPropertyOf axAnns subAnnProp supAnnProp =
    keyword subAnnotationPropertyOfS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, [subAnnProp, supAnnProp]])

printAnnotationPropertyDomain :: AxiomAnnotations -> AnnotationProperty
    -> IRI -> Doc
printAnnotationPropertyDomain axAnns annProp iri =
    keyword annotationPropertyDomainS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, [annProp, iri]])

printAnnotationPropertyRange :: AxiomAnnotations -> AnnotationProperty
    -> IRI -> Doc
printAnnotationPropertyDomain axAnns annProp iri =
    keyword annotationPropertyRangeS
    <> sParens (hsep . concat . map (map pretty) $
        [axAnns, [annProp, iri]])
