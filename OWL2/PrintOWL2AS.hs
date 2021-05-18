module OWL2.PrintOWL2AS where

import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Keywords
import Common.IRI

import OWL2.AS
import OWL2.Keywords
import OWL2.ColonKeywords
import OWL2.ASKeywords

import Data.List

-- | auxiliary parens function
sParens d = parens (space <> d <> space)

-- | print IRI
printIRI :: [String] -> IRI -> Doc
printIRI ontPrefs iri
    | isAbbrev iri && elem prefName ontPrefs = 
        text (prefName ++ ":" ++ (iFragment iri)))
    | otherwise = pretty iri
  where prefName = prefixName iri

printDataIRI :: IRI -> Doc
printDataIRI q = if isDatatypeKey q then text $ showIRI $ setDatatypePrefix q
    else pretty q

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
        where 
            entityTypeS = case ty of
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
        <> sParens (hsep . concat $ [[pretty dt], fvsUnwrapped])
    where fvsUnwrapped = concat [[pretty f, pretty v] | (f, v) <- fvs]

printDataJunction :: JunctionType -> [DataRange] -> Doc
printDataJunction jt drs = junctionKeyword <> sParens (hsep . map pretty $ drs)
    where 
        junctionKeyword = case jt of 
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
    where 
        junctionKeyword = case jt of
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
    quantifierKeyword <> sParens (hsep [pretty obPropExpr, pretty clexpr])
    where
        quantifierKeyword = case qt of
            AllValuesFrom -> keyword objectAllValuesFromS
            SomeValuesFrom -> keyword objectSomeValuesFromS

printObjectHasValue :: ObjectPropertyExpression -> Individual -> Doc
printObjectHasValue objPropExpr ind = keyword objectHasValueS
    <> sParens (hsep [pretty objPropExpr, pretty ind])

printObjectHasSelf :: ObjectPropertyExpression -> Doc
printObjectHasSelf objPropExpr = keyword objectHasSelfS
    <> sParens (pretty objPropExpr)

printObjectCardinality :: Cardinality ObjectPropertyExpression ClassExpression
    -> Doc
printObjectCardinality card =
    cardinalityKeyword <> sParens (hsep $
        [text $ show n, pretty objPropExpr, clExpr])
    where
        (Cardinality cardType n objPropExpr mClExpr) = card
        cardinalityKeyword = case cardType of
            MaxCardinality -> keyword objectMaxCardinalityS
            MinCardinality -> keyword objectMinCardinalityS
            ExactCardinality -> keyword objectExactCardinalityS
        clExpr = case mClExpr of
            Nothing -> empty
            Just clexpr -> pretty clexpr

printDataValuesFrom :: QuantifierType -> [DataPropertyExpression] -> DataRange
    -> Doc
printDataValuesFrom qt dPropExprs dr =
    quantifierKeyword <> sParens (hsep . concat $
        [map pretty dPropExprs, [pretty dr]])
    where
        quantifierKeyword = case qt of
            AllValuesFrom -> keyword dataAllValuesFromS
            SomeValuesFrom -> keyword dataSomeValuesFromS

printDataCardinality :: Cardinality DataPropertyExpression DataRange -> Doc
printDataCardinality card = cardinalityKeyword <> sParens (hsep $
        [text $ show n, pretty dataPropExpr, dr])
    where
        (Cardinality cardType n dataPropExpr mDr) = card
        cardinalityKeyword = case cardType of
            MaxCardinality -> keyword dataMaxCardinalityS
            MinCardinality -> keyword dataMinCardinalityS
            ExactCardinality -> keyword dataExactCardinalityS
        dr = case mDr of
            Nothing -> empty
            Just drange -> pretty drange

printDataHasValue :: DataPropertyExpression -> Literal -> Doc
printDataHasValue dPropExpr lit = 
    keyword dataHasValueS <> sParens(hsep [pretty dPropExpr, pretty lit])

-- | print Annotations

instance Pretty AnnotationValue where
    pretty anVal = case anVal of
        AnnAnInd anInd -> doubleQuotes . text $ anInd
        AnnValue iri -> pretty iri
        AnnValLit lit -> pretty lit

instance Pretty Annotation where
    pretty (Annotation ans anProp anVal) =
        keyword annotationS <> sParens (hsep . concat $
            [map pretty ans, [pretty anProp, pretty anVal]])

instance Pretty AnnotationSubject where
    pretty annSub = case annSub of
        AnnSubIri iri -> pretty iri
        AnnSubAnInd ind -> doubleQuotes . text $ ind

-- | print Axioms

instance Pretty Axiom where
    pretty axiom = case axiom of
        Declaration axAnns ent ->
            keyword "Declaration"
            <> sParens (hsep . concat $
                [map pretty axAnns, [pretty ent]])

        ClassAxiom ax -> pretty ax
        ObjectPropertyAxiom ax -> pretty ax
        DataPropertyAxiom ax -> pretty ax
        DatatypeDefinition axAnns dt dr 
            -> printDatatypeDefinition axAnns dt dr
        HasKey axAnns clExpr objPropExprs dataPropExprs
            -> printHasKey axAnns clExpr objPropExprs dataPropExprs
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
    <> sParens (hsep . concat $
        [map pretty axAnns, map pretty [subClExpr, supClExpr]])

printEquivalentClasses :: AxiomAnnotations -> [ClassExpression] -> Doc
printEquivalentClasses axAnns clExprs =
    keyword equivalentClassesS
    <> sParens (hsep . concat $
        [map pretty axAnns, map pretty clExprs])

printDisjointClasses :: AxiomAnnotations -> [ClassExpression] -> Doc
printDisjointClasses axAnns clExprs =
    keyword disjointClassesS
    <> sParens (hsep . concat $
        [map pretty axAnns, map pretty clExprs])

printDisjointUnion ::AxiomAnnotations -> Class -> DisjointClassExpression 
    -> Doc
printDisjointUnion axAnns cl disjClExprs = 
    keyword disjointUnionS
    <> sParens (hsep . concat $
        [map pretty axAnns, [pretty cl], map pretty disjClExprs])

-- | print SubObjectProperyExpression
printSubObjectPropertyExpression :: [PrefixDeclaration]
    -> SubObjectPropertyExpression -> Doc
printSubObjectPropertyExpression pds subObjPropExpr =
    case subObjPropExpr of
        SubObjPropExpr_obj objPropExpr
            -> printObjectPropertyExpression pds objPropExpr
        SubObjPropExpr_exprchain propExprChain
            -> keyword objectPropertyChainS 
                <> sParens (hsep
                    . map (printObjectPropertyExpression pds) $ propExprChain)

-- | print ObjectPropertyAxiom
printObjectPropertyAxiom :: [PrefixDeclaration] -> ObjectPropertyAxiom -> Doc
printObjectPropertyAxiom pds objPropAx = case objPropAx of
    SubObjectPropertyOf axAnns subObjPropExpr supObjPropExpr
        -> printSubObjectPropertyOf pds axAnns subObjPropExpr supObjPropExpr
    EquivalentObjectProperties axAnns objPropExprs
        -> printEquivalentObjectProperties pds axAnns objPropExprs
    DisjointObjectProperties axAnns objPropExprs
        -> printDisjointObjectProperties pds axAnns objPropExprs
    InverseObjectProperties axAnns objPropExpr1 objPropExpr2
        -> printInverseObjectProperties pds axAnns objPropExpr1 objPropExpr2
    ObjectPropertyDomain axAnns objPropExpr clExpr
        -> printObjectPropertyDomain pds axAnns objPropExpr clExpr
    ObjectPropertyRange axAnns objPropExpr clExpr
        -> printObjectPropertyRange pds axAnns objPropExpr clExpr
    FunctionalObjectProperty axAnns objPropExpr
        -> printFunctionalObjectProperty pds axAnns objPropExpr
    InverseFunctionalObjectProperty axAnns objPropExpr
        -> printInverseFunctionalObjectProperty pds axAnns objPropExpr
    ReflexiveObjectProperty axAnns objPropExpr
        -> printReflexiveObjectProperty pds axAnns objPropExpr
    IrreflexiveObjectProperty axAnns objPropExpr
        -> printIrreflexiveObjectProperty pds axAnns objPropExpr
    SymmetricObjectProperty axAnns objPropExpr
        -> printSymmetricObjectProperty pds axAnns objPropExpr
    AsymmetricObjectProperty axAnns objPropExpr
        -> printAsymmetricObjectProperty pds axAnns objPropExpr
    TransitiveObjectProperty axAnns objPropExpr
        -> printTransitiveObjectProperty pds axAnns objPropExpr

printSubObjectPropertyOf :: [PrefixDeclaration] -> AxiomAnnotations
    -> SubObjectPropertyExpression -> SuperObjectPropertyExpression -> Doc
printSubObjectPropertyOf pds axAnns subObjPropExpr supObjPropExpr =
    keyword subObjectPropertyOfS
    <> sParens (hsep . concat $ 
        [docAxAnns, [docSubObjPropExpr, docSupObjPropExpr]])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docSubObjPropExpr = printSubObjectPropertyExpression pds subObjPropExpr
        docSupObjPropExpr = printObjectPropertyExpression pds supObjPropExpr

printEquivalentObjectProperties :: [PrefixDeclaration] -> AxiomAnnotations
    -> [ObjectPropertyExpression] -> Doc
printEquivalentObjectProperties pds axAnns objPropExprs =
    keyword equivalentObjectPropertiesS
    <> sParens (hsep . concat $
        [docAxAnns, docObjPropExprs])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docObjPropExprs = map (printObjectPropertyExpression pds) objPropExprs

printDisjointObjectProperties :: [PrefixDeclaration] -> AxiomAnnotations
    -> [ObjectPropertyExpression] -> Doc
printDisjointObjectProperties pds axAnns objPropExprs =
    keyword disjointObjectPropertiesS
    <> sParens (hsep . concat $
        [docAxAnns, docObjPropExprs])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docObjPropExprs = map (printObjectPropertyExpression pds) objPropExprs

printInverseObjectProperties :: [PrefixDeclaration] -> AxiomAnnotations
    -> ObjectPropertyExpression -> ObjectPropertyExpression -> Doc
printInverseObjectProperties pds axAnns objPropExpr1 objPropExpr2 =
    keyword inverseObjectPropertiesS
    <> sParens (hsep . concat $ 
        [docAxAnns, [docObjPropExpr1, docObjPropExpr2]])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docObjPropExpr1 = printObjectPropertyExpression pds objPropExpr1
        docObjPropExpr2 = printObjectPropertyExpression pds objPropExpr2


printObjectPropertyDomain :: [PrefixDeclaration] -> AxiomAnnotations
    -> ObjectPropertyExpression -> ClassExpression -> Doc
printObjectPropertyDomain pds axAnns objPropExpr clExpr =
    keyword objectPropertyDomainS
    <> sParens (hsep . concat $ 
        [docAxAnns, [docObjPropExpr, docClassExpr]])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docObjPropExpr = printObjectPropertyExpression pds objPropExpr
        docClassExpr = printClassExpression pds clExpr

printObjectPropertyRange :: [PrefixDeclaration] -> AxiomAnnotations
    -> ObjectPropertyExpression -> ClassExpression -> Doc
printObjectPropertyRange pds axAnns objPropExpr clExpr = 
    keyword objectPropertyRangeS
    <> sParens (hsep . concat $ 
        [[docAxAnns, [docObjPropExpr, docClassExpr]])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docObjPropExpr = printObjectPropertyExpression pds objPropExpr
        docClassExpr = printClassExpression pds clExpr
    

printFunctionalObjectProperty :: [PrefixDeclaration] -> AxiomAnnotations
    -> ObjectPropertyExpression -> Doc
printFunctionalObjectProperty pds axAnns objPropExpr =
    keyword functionalObjectPropertyS
    <> sParens (hsep . concat $
        [docAxAnns, [docObjPropExpr]])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docObjPropExpr = printObjectPropertyExpression pds objPropExpr

printInverseFunctionalObjectProperty :: [PrefixDeclaration] -> AxiomAnnotations
    -> ObjectPropertyExpression -> Doc
printInverseFunctionalObjectProperty pds axAnns objPropExpr =
    keyword inverseFunctionalObjectPropertyS
    <> sParens (hsep . concat $
        [docAxAnns, [docObjPropExpr]])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docObjPropExpr = printObjectPropertyExpression pds objPropExpr

printReflexiveObjectProperty :: [PrefixDeclaration] -> AxiomAnnotations
    -> ObjectPropertyExpression -> Doc
printReflexiveObjectProperty pds axAnns objPropExpr =
    keyword reflexiveObjectPropertyS
    <> sParens (hsep . concat $
        [docAxAnns, [docObjPropExpr]])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docObjPropExpr = printObjectPropertyExpression pds objPropExpr


printIrreflexiveObjectProperty :: [PrefixDeclaration] -> AxiomAnnotations
    -> ObjectPropertyExpression -> Doc
printIrreflexiveObjectProperty pds axAnns objPropExpr =
    keyword irreflexiveObjectPropertyS
    <> sParens (hsep . concat $
        [docAxAnns, [docObjPropExpr]])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docObjPropExpr = printObjectPropertyExpression pds objPropExpr

printSymmetricObjectProperty :: [PrefixDeclaration] -> AxiomAnnotations
    -> ObjectPropertyExpression -> Doc
printSymmetricObjectProperty pds axAnns objPropExpr =
    keyword symmetricObjectPropertyS
    <> sParens (hsep . concat $
        [docAxAnns, [docObjPropExpr]])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docObjPropExpr = printObjectPropertyExpression pds objPropExpr

printAsymmetricObjectProperty :: [PrefixDeclaration] -> AxiomAnnotations
    -> ObjectPropertyExpression -> Doc
printAsymmetricObjectProperty pds axAnns objPropExpr =
    keyword asymmetricObjectPropertyS
    <> sParens (hsep . concat $
        [docAxAnns, [docObjPropExpr]])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docObjPropExpr = printObjectPropertyExpression pds objPropExpr

printTransitiveObjectProperty :: [PrefixDeclaration] -> AxiomAnnotations
    -> ObjectPropertyExpression -> Doc
printTransitiveObjectProperty axAnns objPropExpr =
    keyword transitiveObjectPropertyS
    <> sParens (hsep . concat $
        [docAxAnns, [docObjPropExpr]])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docObjPropExpr = printObjectPropertyExpression pds objPropExpr

-- | print DataPropertyAxiom
printDataPropertyAxiom :: [PrefixDeclaration] -> DataPropertyAxiom -> Doc
printDataPropertyAxiom pds dpAx = case dpAx of
    SubDataPropertyOf axAnns subDataPropExpr supDataPropExpr
        -> printSubDataPropertyOf pds axAnns subDataPropExpr supDataPropExpr
    EquivalentDataProperties axAnns dataPropExprs
        -> printEquivalentDataProperties pds axAnns dataPropExprs
    DisjointDataProperties axAnns dataPropExprs
        -> printDisjointDataProperties pds axAnns dataPropExprs
    DataPropertyDomain axAnns dataPropExpr clExpr
        -> printDataPropertyDomain pds axAnns dataPropExpr clExpr
    DataPropertyRange axAnns dataPropExpr dr
        -> printDataPropertyRange pds axAnns dataPropExpr dr
    FunctionalDataProperty axAnns dataPropExpr
        -> printFunctionalDataProperty pds axAnns dataPropExpr

printSubDataPropertyOf :: [PrefixDeclaration] -> AxiomAnnotations ->
    SubDataPropertyExpression -> SuperDataPropertyExpression -> Doc
printSubDataPropertyOf pds axAnns subDataPropExpr supDataPropExpr = 
    keyword subDataPropertyOfS
    <> sParens (hsep . concat $
        [docAxAnns, [docSubDataPropExpr, docSupDataPropExpr]])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docSubDataPropExpr = printIRI pds subDataPropExpr
        docSupDatapropExpr = printIRI pds supDataPropExpr

printEquivalentDataProperties :: [PrefixDeclaration] -> AxiomAnnotations
    -> [DataPropertyExpression] -> Doc
printEquivalentDataProperties pds axAnns dataPropExprs =
    keyword equivalentDataPropertiesS
    <> sParens (hsep . concat  $
        [docAxAnns, docDataPropExprs])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docDataPropExprs = map (printIRI pds) dataPropExprs

printDisjointDataProperties :: [PrefixDeclaration] -> AxiomAnnotations
    -> [DataPropertyExpression] -> Doc
printDisjointDataProperties pds axAnns dataPropExprs =
    keyword disjointDataPropertiesS
    <> sParens (hsep . concat $
        [docAxAnns, docDataPropExprs])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docDataPropExprs = map (printIRI pds) dataPropExprs

printDataPropertyDomain :: [PrefixDeclaration] -> AxiomAnnotations
    -> DataPropertyExpression -> ClassExpression -> Doc
printDataPropertyDomain pds axAnns dataPropExpr clExpr =
    keyword dataPropertyDomainS
    <> sParens (hsep . concat $
        [docAxAnns, [docDataPropExpr, docClassExpr]])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docDataPropExpr = printIRI pds dataPropExpr
        docClassExpr = printClassExpression pds clExpr

printDataPropertyRange  :: [PrefixDeclaration] -> AxiomAnnotations 
    -> DataPropertyExpression -> DataRange -> Doc
printDataPropertyRange  axAnns dataPropExpr dr =
    keyword dataPropertyRangeS
    <> sParens (hsep . concat $
        [docAxAnns, [docDataPropExpr, docDataRange]])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docDataPropExpr = printIRI pds dataPropExpr
        docDataRange = printDataRange pds dr

printFunctionalDataProperty :: [PrefixDeclaration] -> AxiomAnnotations
    -> DataPropertyExpression -> Doc
printFunctionalDataProperty axAnns dataPropExpr =
    keyword functionalDataPropertyS
    <> sParens (hsep . concat $ 
        [docAxAnns, [docDataPropExpr]])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docDataPropExpr = printIRI pds dataPropExpr

-- | print DatatypeDefinition axiom

printDatatypeDefinition :: [PrefixDeclaration] -> AxiomAnnotations -> Datatype
    -> DataRange -> Doc
printDatatypeDefinition pds axAnns dt dr =
    keyword datatypeDefinitionS
    <> sParens (hsep . concat $
        [docAxAnns, [docDt, docDr]])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docDt = printIRI pds dt
        docDr = printDataRange pds dr

-- | print HasKey axiom

printHasKey :: [PrefixDeclaration] -> AxiomAnnotations -> ClassExpression
    -> [ObjectPropertyExpression] -> [DataPropertyExpression] -> Doc
printHasKey pds axAnns clExpr objPropExprs dataPropExprs =
    keyword hasKeyS
    <> sParens (hsep . concat $
        [docAxAnns, [docClassExpr, docObjPropExprs, docDataPropExprs]])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docClassExpr = printClassExpression pds clExpr
        docObjPropExprs = sParens . hsep
            . map (printObjectPropertyExpression pds) $ objPropExprs
        docDataPropExprs = sParens . hsep
            . map (printIRI pds) $ dataPropExprs

-- | print Assertion axiom
printAssertion :: [PrefixDeclaration] -> Assertion -> Doc
printAssertion pds assertion = case assertion of
    SameIndividual axAnns inds -> printSameIndividual pds axAnns inds
    DifferentIndividuals axAnns inds
        -> printDifferentIndividuals pds axAnns inds
    ClassAssertion axAnns clExpr ind
        -> printClassAssertion pds axAnns clExpr ind
    ObjectPropertyAssertion axAnns objPropExpr srcInd targInd
        -> printObjectPropertyAssertion pds axAnns objPropExpr srcInd targInd
    NegativeObjectPropertyAssertion axAnns objPropExpr srcInd targInd
        -> printNegativeObjectPropertyAssertion pds axAnns objPropExpr srcInd
            targInd
    DataPropertyAssertion axAnns dataPropExpr srcInd targVal
        -> printDataPropertyAssertion pds axAnns dataPropExpr srcInd targVal
    NegativeDataPropertyAssertion axAnns dataPropExpr srcInd targVal
        -> printNegativeDataPropertyAssertion pds axAnns dataPropExpr srcInd
            targVal

printSameIndividual :: [PrefixDeclaration] -> AxiomAnnotations -> [Individual]
    -> Doc
printSameIndividual pds axAnns inds =
    keyword sameIndividualS
    <> sParens (hsep . concat $
        [docAxAnns, docInds])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docInds = map (printIRI pds) inds

printDifferentIndividuals :: [PrefixDeclaration] -> AxiomAnnotations
    -> [Individual] -> Doc
printDifferentIndividuals pds axAnns inds =
    keyword differentIndividualsS
    <> sParens (hsep . concat $
        [docAxAnns, docInds])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docInds = map (printIRI pds) inds

printClassAssertion :: [PrefixDeclaration] -> AxiomAnnotations
    -> ClassExpression -> Individual -> Doc
printClassAssertion pds axAnns clExpr ind =
    keyword classAssertionS
    <> sParens (hsep . concat $
        [docAxAnns, [docClassExpr, docInd]])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docClassExpr = printClassExpression pds clExpr
        docInd = printIRI pds ind

printObjectPropertyAssertion :: [PrefixDeclaration] -> AxiomAnnotations
    -> ObjectPropertyExpression -> SourceIndividual -> TargetIndividual -> Doc
printObjectPropertyAssertion pds axAnns objPropExpr srcInd targInd =
    keyword objectPropertyAssertionS
    <> sParens (hsep . concat $
        [docAxAnns, [docObjPropExpr, docSrcInd, docTargInd]])
    where 
        docAxAnns = map (printAnnotation pds) axAnns
        docObjPropExpr = printObjectPropertyExpression pds objPropExpr
        docSrcInd = printIRI pds srcInd
        docTargInd = printIRI pds targInd


printNegativeObjectPropertyAssertion :: [PrefixDeclaration] -> AxiomAnnotations
    -> ObjectPropertyExpression -> SourceIndividual -> TargetIndividual -> Doc
printNegativeObjectPropertyAssertion pds axAnns objPropExpr srcInd targInd =
    keyword negativeObjectPropertyAssertionS
    <> sParens (hsep . concat $
        [docAxAnns, [docObjPropExpr, docSrcInd, docTargInd]])
    where 
        docAxAnns = map (printAnnotation pds) axAnns
        docObjPropExpr = printObjectPropertyExpression pds objPropExpr
        docSrcInd = printIRI pds srcInd
        docTargInd = printIRI pds targInd

printDataPropertyAssertion :: [PrefixDeclaration] -> AxiomAnnotations
    -> DataPropertyExpression -> SourceIndividual -> TargetValue -> Doc
printDataPropertyAssertion pds axAnns dataPropExpr srcInd targVal =
    keyword dataPropertyAssertionS
    <> sParens (hsep . concat $
      [docAxAnns, [docDataPropExpr, docSrcInd, docTargInd]])
     where 
        docAxAnns = map (printAnnotation pds) axAnns
        docDataPropExpr = printIRI pds dataPropExpr
        docSrcInd = printIRI pds srcInd
        docTargInd = printIRI pds targInd

printNegativeDataPropertyAssertion :: [PrefixDeclaration] -> AxiomAnnotations
    -> DataPropertyExpression -> SourceIndividual -> TargetValue -> Doc
printNegativeDataPropertyAssertion pds axAnns dataPropExpr srcInd targVal =
    keyword negativeDataPropertyAssertionS
    <> sParens (hsep . concat $
         [docAxAnns, [docDataPropExpr, docSrcInd, docTargInd]])
     where 
        docAxAnns = map (printAnnotation pds) axAnns
        docDataPropExpr = printIRI pds dataPropExpr
        docSrcInd = printIRI pds srcInd
        docTargInd = printIRI pds targInd

-- | print AnnotationAxiom
printAnnotationAxiom :: [PrefixDeclaration] -> AnnotationAxiom -> Doc
printAnnotationAxiom pds annAxs = case annAxs of
    AnnotationAssertion axAnns annProp annSub annValue
            -> printAnnotationAssertion pds axAnns annProp annSub annValue
        SubAnnotationPropertyOf pds axAnns subAnnProp supAnnProp
            -> printSubAnnotationPropertyOf pds axAnns subAnnProp supAnnProp
        AnnotationPropertyDomain pds axAnns annProp iri
            -> printAnnotationPropertyDomain pds axAnns annProp iri
        AnnotationPropertyRange pds axAnns annProp iri
            -> printAnnotationPropertyRange pds axAnns annProp iri

printAnnotationAssertion :: [PrefixDeclaration] -> AxiomAnnotations
    -> AnnotationProperty -> AnnotationSubject ->  AnnotationValue -> Doc
printAnnotationAssertion pds xAnns annProp annSub annValue =
    keyword annotationAssertionS
    <> sParens (hsep . concat $
        [docAxAnns, [docAnnProp, docAnnSub, docAnnValue]])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docAnnProp = printIRI pds annProp
        docAnnSub = printAnnotationSubject pds annSub
        docAnnValue = printAnnotationValue pds annValue

printSubAnnotationPropertyOf :: [PrefixDeclaration] -> AxiomAnnotations
    -> SubAnnotationProperty -> SuperAnnotationProperty -> Doc
printSubAnnotationPropertyOf pds axAnns subAnnProp supAnnProp =
    keyword subAnnotationPropertyOfS
    <> sParens (hsep . concat $ [docAxAnns, [docSubAnnProp, docSupAnnProp]])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docSubAnnProp  = printIRI pds subAnnProp
        docSupAnnProp = printIRI pds supAnnProp


printAnnotationPropertyDomain :: [PrefixDeclaration] -> AxiomAnnotations
    -> AnnotationProperty -> IRI -> Doc
printAnnotationPropertyDomain pds axAnns annProp iri =
    keyword annotationPropertyDomainS
    <> sParens (hsep . concat $
        [docAxAnns, [docAnnProp, docIri]])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docAnnProp = printIRI pds annProp
        docIri = printIRI pds iri    

printAnnotationPropertyRange :: [PrefixDeclaration] -> AxiomAnnotations
    -> AnnotationProperty -> IRI -> Doc
printAnnotationPropertyRange pds axAnns annProp iri =
    keyword annotationPropertyRangeS
    <> sParens (hsep . concat $
        [docAxAnns, [docAnnProp, docIri]])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docAnnProp = printIRI pds annProp
        docIri = printIRI pds iri

-- | print Root
instance Pretty PrefixDeclaration where
    pretty (PrefixDeclaration prName iri) =
        keyword "Prefix"
        <> sParens ((text prName) <> (text " = ") <> pretty iri)

printOnt :: [PrefixDeclaration] -> Ontology -> Doc
printOnt pds (Ontology mOnt mVerIri dImpDocs ontAnns axioms) =
    keyword "Ontology"
    <> sParens (vsep . concat $
    [[ontNameDoc], importedDocs, ontAnnsDocs, axiomsDocs])
    where
        ontAnnsDocs = map (printAnnotation pds) ontAnns
        axiomsDocs = map (printAxiom pds) axioms
        versionIriDoc = maybe empty (printIRI pds) mVerIri
        ontNameDoc = naybe empty (\ontvalue -> hsep [printIRI pds ontvalue,
            versionIriDoc]) mOnt
        importedDocs = keyword "Import"
            <> sParens(hsep . map (printIRI pds) dImpDocs)

instance Pretty OntologyDocument where
    pretty (OntologyDocument prefDecls ont) = 
        (hsep . map pretty $ prefDecls) $+$ printOnt prefDecls ont
