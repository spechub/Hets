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
printIRI :: [PrefixDeclaration] -> IRI -> Doc
printIRI pds iri
    | containsPrefix pds prefName = 
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
printLiteral pds lit = case lit of 
    Literal lexi ty -> plainText ('"' : escapeString False lexi ++ "\"")
        <> literalTail ty
    NumberLit f -> text (show f)
    where literalTail ty = case ty of
            Typed iri -> keyword cTypeS <> printDataIRI pds iri
            Untyped tag -> case tag of
                Nothing -> empty
                Just tg -> text asP <> text tg

escapeString :: Bool -> String -> String
escapeString _ [] = []
escapeString True ('"':s) = '"' : escapeString False s
escapeString False ('"':s) = '\\' : '"' : escapeString False s
escapeString flag ('\\':s) = '\\' : escapeString (not flag) s
escapeString _ (c:s) = c : escapeString False s 

-- | print PropertyExpression
printObjectPropertyExpression :: [PrefixDeclaration] -> ObjectPropertyExpression
    -> Doc
printObjectPropertyExpression pds obExpr = case obExpr of
    ObjectProp objProp -> printIRI pds objProp
    ObjectInverseOf iObjPropExpr ->
        keyword objectInverseOfS
        <> sParens (printObjectPropertyExpression pds iObjPropExpr)

-- | print Entity
printEntity :: [PrefixDeclaration] -> Entity -> Doc
printEntity pds (Entity _ ty ent) =
    keyword entityTypeS <> sParens (docEnt)
    where
        docEnt = printIRI pds ent
        entityTypeS = case ty of
            Datatype -> "Datatype"
            Class -> "Class"
            ObjectProperty -> "ObjectProperty"
            DataProperty -> "DataProperty"
            AnnotationProperty -> "AnnotationProperty"
            NamedIndividual -> "NamedIndividual"

-- | print DataRanges
printDataRange :: [PrefixDeclaration] -> DataRange -> Doc
printDataRange pds dr = case dr of
    DataType dt fvs -> printDataRestriction pds dt fvs
    DataJunction jt drs -> printDataJunction pds jt drs
    DataComplementOf dr -> printDataComplementOf pds dr
    DataOneOf lits -> printDataOneOf pds lits

printDataRestriction :: [PrefixDeclaration] -> Datatype
    -> [(ConstrainingFacet, RestrictionValue)] -> Doc
printDataRestriction pds dt fvs
    | null fvs = printIRI pds dt
    | otherwise = keyword datatypeRestrictionS
        <> sParens (hsep . concat $ [[docDt], fvsUnwrapped])
    where
        fvsUnwrapped = concat [[printIRI pds f, printLiteral pds v]
            | (f, v) <- fvs]
        docDt = printIRI pds dt

printDataJunction :: [PrefixDeclaration] -> JunctionType -> [DataRange] -> Doc
printDataJunction pds jt drs =
    junctionKeyword <> sParens (hsep docDrs)
    where 
        junctionKeyword = case jt of 
            UnionOf -> keyword dataUnionOfS
            IntersectionOf -> keyword dataIntersectionOfS
        docDrs = map (printDataRange pds) drs

printDataComplementOf :: [PrefixDeclaration] -> DataRange -> Doc
printDataComplementOf pds dr =
    keyword dataComplementOfS <> sParens docDr
    where docDr = printDataRange pds dr

printDataOneOf :: [PrefixDeclaration] -> [Literal] -> Doc
printDataOneOf pds lits = keyword dataOneOfS
    <> sParens (hsep . map (printLiteral pds) $ lits)

-- | print ClassExpressions
printClassExpression :: [PrefixDeclaration] -> ClassExpression -> Doc
printClassExpression pds clExpr = case clExpr of
    Expression cl -> printIRI pds cl
    ObjectJunction jt clExprs -> printObjectJunction pds jt clExprs
    ObjectComplementOf clexpr -> printObjectComplementOf pds clexpr
    ObjectOneOf inds -> printObjectOneOf pds inds
    ObjectValuesFrom qt obPropExpr clexpr ->
        printObjectValuesFrom pds qt obPropExpr clexpr
    ObjectHasValue objPropExpr ind ->
        printObjectHasValue pds objPropExpr ind
    ObjectHasSelf objPropExpr -> printObjectHasSelf pds objPropExpr
    ObjectCardinality card -> printObjectCardinality pds card
    DataValuesFrom qt dPropExprs dr ->
        printDataValuesFrom pds qt dPropExprs dr
    DataHasValue dPropExpr lit -> printDataHasValue pds dPropExpr lit
    DataCardinality card -> printDataCardinality pds card

printObjectJunction :: [PrefixDeclaration] -> JunctionType
    -> [ClassExpression] -> Doc
printObjectJunction pds jt clExprs =
    junctionKeyword <> sParens (hsep docClExprs)
    where 
        junctionKeyword = case jt of
            UnionOf -> keyword objectUnionOfS
            IntersectionOf -> keyword objectIntersectionOfS
        docClExprs = map (printClassExpression pds) clExprs

printObjectComplementOf :: [PrefixDeclaration] -> ClassExpression -> Doc
printObjectComplementOf pds clExpr =
    keyword objectComplementOfS <> sParens (docClExpr)
    where docClExpr = printClassExpression pds clExpr

printObjectOneOf :: [PrefixDeclaration] -> [Individual] -> Doc
printObjectOneOf pds inds =
    keyword objectOneOfS <> sParens (hsep docInds)
    where docInds = map (printIRI pds) inds

printObjectValuesFrom :: [PrefixDeclaration] -> QuantifierType
    -> ObjectPropertyExpression -> ClassExpression -> Doc
printObjectValuesFrom pds qt obPropExpr clExpr =
    quantifierKeyword <> sParens (hsep [docObPropExpr, docClExpr])
    where
        quantifierKeyword = case qt of
            AllValuesFrom -> keyword objectAllValuesFromS
            SomeValuesFrom -> keyword objectSomeValuesFromS
        docObPropExpr = printObjectPropertyExpression pds obPropExpr
        docClExpr = printClassExpression pds clExpr

printObjectHasValue :: [PrefixDeclaration] -> ObjectPropertyExpression
    -> Individual -> Doc
printObjectHasValue pds objPropExpr ind =
    keyword objectHasValueS <> sParens (hsep [docObjPropExpr, docInd])
    where
        docObjPropExpr = printObjectPropertyExpression pds objPropExpr
        docInd = printIRI pds ind

printObjectHasSelf :: [PrefixDeclaration] -> ObjectPropertyExpression -> Doc
printObjectHasSelf pds objPropExpr =
    keyword objectHasSelfS <> sParens docObjPropExpr
    where docObjPropExpr = printObjectPropertyExpression pds objPropExpr

printObjectCardinality :: [PrefixDeclaration] 
    -> Cardinality ObjectPropertyExpression ClassExpression -> Doc
printObjectCardinality pds card =
    cardinalityKeyword <> sParens (hsep $
        [text $ show n, docObjPropExpr, docClExpr])
    where
        (Cardinality cardType n objPropExpr mClExpr) = card
        cardinalityKeyword = case cardType of
            MaxCardinality -> keyword objectMaxCardinalityS
            MinCardinality -> keyword objectMinCardinalityS
            ExactCardinality -> keyword objectExactCardinalityS
        docObjPropExpr = printObjectPropertyExpression pds objPropExpr
        docClExpr = case mClExpr of
            Nothing -> empty
            Just clExpr -> printClassExpression pds clExpr

printDataValuesFrom :: [PrefixDeclaration] -> QuantifierType
    -> [DataPropertyExpression] -> DataRange -> Doc
printDataValuesFrom pds qt dPropExprs dr =
    quantifierKeyword <> sParens (hsep . concat $
        [docDPropExprs, [docDr]])
    where
        quantifierKeyword = case qt of
            AllValuesFrom -> keyword dataAllValuesFromS
            SomeValuesFrom -> keyword dataSomeValuesFromS
        docDPropExprs = map (printIRI pds) dPropExprs
        docDr = printDataRange pds dr

printDataCardinality :: [PrefixDeclaration]
    -> Cardinality DataPropertyExpression DataRange -> Doc
printDataCardinality pds card = cardinalityKeyword <> sParens (hsep $
        [text $ show n, docDataPropExpr, docDr])
    where
        (Cardinality cardType n dataPropExpr mDr) = card
        cardinalityKeyword = case cardType of
            MaxCardinality -> keyword dataMaxCardinalityS
            MinCardinality -> keyword dataMinCardinalityS
            ExactCardinality -> keyword dataExactCardinalityS
        docDataPropExpr = printIRI pds dataPropExpr
        docDr = case mDr of
            Nothing -> empty
            Just drange -> printDataRange pds drange

printDataHasValue :: [PrefixDeclaration] -> DataPropertyExpression
    -> Literal -> Doc
printDataHasValue pds dPropExpr lit = 
    keyword dataHasValueS <> sParens(hsep [docDPropExpr, docLit])
    where
        docDPropExpr = printIRI pds dPropExpr
        docLit = printLiteral pds lit

-- | print Annotations
printAnnotationValue :: [PrefixDeclaration] -> AnnotationValue -> Doc
printAnnotationValue pds anVal = case anVal of
    AnnAnInd anInd -> printIRI pds anInd
    AnnValue iri -> printIRI pds iri
    AnnValLit lit -> printLiteral pds lit

printAnnotation :: [PrefixDeclaration] -> Annotation -> Doc
printAnnotation pds (Annotation ans anProp anVal) =
    keyword annotationS <> sParens (hsep . concat $
        [docAns, [docAnProp, docAnVal]])
    where
        docAns = map (printAnnotation pds) ans
        docAnProp = printIRI pds anProp
        docAnVal = printAnnotationValue pds anVal

printAnnotationSubject :: [PrefixDeclaration] -> AnnotationSubject -> Doc
printAnnotationSubject pds annSub = case annSub of
    AnnSubIri iri -> printIRI pds iri
    AnnSubAnInd ind -> printIRI pds ind

-- | print Axioms
printAxiom :: [PrefixDeclaration] -> Axiom -> Doc
printAxiom pds axiom = case axiom of 
    Declaration axAnns ent -> printDeclaration pds axAnns ent
    ClassAxiom ax -> printClassAxiom pds ax
    ObjectPropertyAxiom ax -> printObjectPropertyAxiom pds ax
    DataPropertyAxiom ax -> printDataPropertyAxiom pds ax
    DatatypeDefinition axAnns dt dr 
        -> printDatatypeDefinition pds axAnns dt dr
    HasKey axAnns clExpr objPropExprs dataPropExprs
        -> printHasKey pds axAnns clExpr objPropExprs dataPropExprs
    Assertion ax -> printAssertion pds ax
    AnnotationAxiom ax -> printAnnotationAxiom pds ax

printDeclaration :: [PrefixDeclaration] -> AxiomAnnotations -> Entity -> Doc
printDeclaration pds axAnns ent =
    keyword "Declaration"
    <> sParens (hsep . concat $
        [docAxAnns, [docEnt]])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docEnt = printEntity pds ent

-- | print ClassAxiom
printClassAxiom :: [PrefixDeclaration] -> ClassAxiom -> Doc
printClassAxiom pds ca = case ca of
    SubClassOf axAnns subClExpr supClExpr ->
        printSubClassOf pds axAnns subClExpr supClExpr
    EquivalentClasses axAnns clExprs ->
        printEquivalentClasses pds axAnns clExprs
    DisjointClasses axAnns clExprs -> printDisjointClasses pds axAnns clExprs
    DisjointUnion axAnns cl disjClExprs ->
        printDisjointUnion pds axAnns cl disjClExprs

printSubClassOf :: [PrefixDeclaration] -> AxiomAnnotations
    -> SubClassExpression -> SuperClassExpression -> Doc
printSubClassOf pds axAnns subClExpr supClExpr =
    keyword subClassOfS
    <> sParens (hsep . concat $
        [docAxAnns, [docSubClExpr, docSupClExpr]])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docSubClExpr = printClassExpression pds subClExpr
        docSupClExpr = printClassExpression pds supClExpr

printEquivalentClasses :: [PrefixDeclaration] -> AxiomAnnotations
    -> [ClassExpression] -> Doc
printEquivalentClasses pds axAnns clExprs =
    keyword equivalentClassesS
    <> sParens (hsep . concat $
        [docAxAnns, docClExprs])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docClExprs = map (printClassExpression pds) clExprs

printDisjointClasses :: [PrefixDeclaration] -> AxiomAnnotations
    -> [ClassExpression] -> Doc
printDisjointClasses pds axAnns clExprs =
    keyword disjointClassesS
    <> sParens (hsep . concat $
        [docAxAnns, docClExprs])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docClExprs = map (printClassExpression pds) clExprs

printDisjointUnion :: [PrefixDeclaration] -> AxiomAnnotations -> Class
    -> DisjointClassExpression  -> Doc
printDisjointUnion pds axAnns cl disjClExprs = 
    keyword disjointUnionS
    <> sParens (hsep . concat $
        [docAxAnns, [docCl], docDisjClExprs])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docCl = printIRI pds cl
        docDisjClExprs = map (printClassExpression pds) disjClExprs

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
        [docAxAnns, [docObjPropExpr, docClassExpr]])
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
printTransitiveObjectProperty pds axAnns objPropExpr =
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
        docSupDataPropExpr = printIRI pds supDataPropExpr

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
printDataPropertyRange pds axAnns dataPropExpr dr =
    keyword dataPropertyRangeS
    <> sParens (hsep . concat $
        [docAxAnns, [docDataPropExpr, docDataRange]])
    where
        docAxAnns = map (printAnnotation pds) axAnns
        docDataPropExpr = printIRI pds dataPropExpr
        docDataRange = printDataRange pds dr

printFunctionalDataProperty :: [PrefixDeclaration] -> AxiomAnnotations
    -> DataPropertyExpression -> Doc
printFunctionalDataProperty pds axAnns dataPropExpr =
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
      [docAxAnns, [docDataPropExpr, docSrcInd, docTargVal]])
     where 
        docAxAnns = map (printAnnotation pds) axAnns
        docDataPropExpr = printIRI pds dataPropExpr
        docSrcInd = printIRI pds srcInd
        docTargVal = printLiteral pds targVal

printNegativeDataPropertyAssertion :: [PrefixDeclaration] -> AxiomAnnotations
    -> DataPropertyExpression -> SourceIndividual -> TargetValue -> Doc
printNegativeDataPropertyAssertion pds axAnns dataPropExpr srcInd targVal =
    keyword negativeDataPropertyAssertionS
    <> sParens (hsep . concat $
         [docAxAnns, [docDataPropExpr, docSrcInd, docTargVal]])
     where 
        docAxAnns = map (printAnnotation pds) axAnns
        docDataPropExpr = printIRI pds dataPropExpr
        docSrcInd = printIRI pds srcInd
        docTargVal = printLiteral pds targVal

-- | print AnnotationAxiom
printAnnotationAxiom :: [PrefixDeclaration] -> AnnotationAxiom -> Doc
printAnnotationAxiom pds annAxs = case annAxs of
    AnnotationAssertion axAnns annProp annSub annValue
        -> printAnnotationAssertion pds axAnns annProp annSub annValue
    SubAnnotationPropertyOf axAnns subAnnProp supAnnProp
        -> printSubAnnotationPropertyOf pds axAnns subAnnProp supAnnProp
    AnnotationPropertyDomain axAnns annProp iri
        -> printAnnotationPropertyDomain pds axAnns annProp iri
    AnnotationPropertyRange axAnns annProp iri
        -> printAnnotationPropertyRange pds axAnns annProp iri

printAnnotationAssertion :: [PrefixDeclaration] -> AxiomAnnotations
    -> AnnotationProperty -> AnnotationSubject ->  AnnotationValue -> Doc
printAnnotationAssertion pds axAnns annProp annSub annValue =
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
        <> sParens ((text (prName ++ ":")) <> (text " = ") <> pretty iri)

printOnt :: [PrefixDeclaration] -> Ontology -> Doc
printOnt pds (Ontology mOnt mVerIri dImpDocs ontAnns axioms) =
    keyword "Ontology"
    <> sParens (vsep . concat $
    [[ontNameDoc], [importedDocs], ontAnnsDocs, axiomsDocs])
    where
        ontAnnsDocs = map (printAnnotation pds) ontAnns
        axiomsDocs = map (printAxiom pds) axioms
        versionIriDoc = maybe empty (printIRI pds) mVerIri
        ontNameDoc = maybe empty (\ontvalue -> hsep [printIRI pds ontvalue,
            versionIriDoc]) mOnt
        importedDocs
            | null dImpDocs = empty
            | otherwise =
                vsep . map ((keyword "Import" <>)
                    . sParens . printIRI pds) $ dImpDocs

instance Pretty OntologyDocument where
    pretty (OntologyDocument prefDecls ont) = 
        (vsep . map pretty $ prefDecls) $+$ printOnt prefDecls ont
