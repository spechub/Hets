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
instance Pretty Individual where
    pretty ind = case ind of
        NamedIndividual_ ni = pretty ni
        AnonymousIndividual ai = doubleQuotes ai

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
    where quantifierKeyword = case qt of
        AllValuesFrom -> keyword objectAllValuesFromS
        SomeValuesFrom -> keyword objectSomeValuesFromS

printObjectHasValue :: ObjectPropertyExpression -> Individual -> Doc
printObjectHasValue objPropExpr ind = keyword objectHasValueS
    <> sParens (hsep . map pretty $ [objPropExpr, ind])

printObjectHasSelf :: ObjectPropertyExpression -> Doc
printObjectHasSelf objPropExpr = keyword objectHasSelfS
    <> sParens (pretty objPropExpr)

-- | print Axioms

instance Pretty AxiomAnnotations where
    pretty = printAnnotations

instance Pretty ClassAxiom where
    pretty ca = case ca of 
        SubClassOf axAns subClExpr supClExpr -> printSubClassOf ca
        EquivalentClasses axAns clExprs -> printEquivalentClasses ca
        DisjointClasses axAns clExprs -> printDisjointClasses ca
        DisjointUnion axAns cl disjClExprs -> printDisjointUnion ca

printSubClassOf :: ClassAxiom -> Doc
printSubClassOf (SubClassOf axAns subClExpr supClExpr) =
    keyword "SubClassOf" <+>
    (sParens . hsep $ (map pretty [axAns, subClExpr, supClExpr]))

printEquivalentClasses :: ClassAxiom -> Doc
printEquivalentClasses (EquivalentClasses axAns clExprs) =
    keyword "EquivalentClasses"
    <> (sParens . hsep . concat $ [[pretty axAns], map pretty clExprs])

printDisjointClasses :: ClassAxiom -> Doc
printDisjointClasses (DisjointClasses axAns clExprs) =
    keyword "DisjointClasses"
    <> (sParens . hsep . concat $ [[pretty axAns], map pretty clExprs])

printDisjointUnion :: ClassAxiom -> Doc
printDisjointUnion (DisjointUnion axAns cl disjClExprs) = 
    keyword "DisjointUnion"
    <> (sParens . hsep . concat $ [map pretty [axAns, cl],
        map pretty disjClExprs])

instance Pretty Axiom where
    pretty axiom = case axiom of
        ClassAxiom ca -> pretty ca
