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

type Annotations = [Annotation]
type FrameId = (String, IRI)
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
        k = ("AnnotationProperty", annProp)
        v = M.findWithDefault M.empty k ms

-- | transform Entity
tEntity :: Entity -> MnchstrSntx -> MnchstrSntx
tEntity entity ms = case (entityKind entity) of
    Datatype ->
        if M.notMember ("Datatype", iri) ms
            then M.insert ("Datatype", iri) M.empty ms
            else ms

    Class -> 
        if M.notMember ("Class", iri) ms
            then M.insert ("Class", iri) M.empty ms
            else ms

    ObjectProperty ->
        if M.notMember ("ObjectProperty", iri) ms
            then M.insert ("ObjectProperty", iri) M.empty ms
            else ms

    DataProperty -> 
        if M.notMember ("DataProperty", iri) ms
            then M.insert ("DataProperty", iri) M.empty ms
            else ms

    AnnotationProperty ->
        if M.notMember ("AnnotationProperty", iri) ms
            then M.insert ("AnnotationProperty", iri) M.empty ms
            else ms
    
    NamedIndividual ->
        if M.notMember ("NamedIndividual", iri) ms
            then M.insert ("NamedIndividual", iri) M.empty ms
            else ms

    where iri = cutIRI entity

-- | transform Class Axiom
tClassAxiom :: ClassAxiom -> MnchstrSntx -> MnchstrSntx
-- SubClassOf axiom
tClassAxiom clAx@(SubClassOf anns subClExpr@(Expression iri) supClExpr) ms = 
    M.insert ("Class", iri) (M.insert "subClassOf" newAxioms m2) m1
    where
        m1 = tClassExpression supClExpr . tAnnotations anns $ ms
        -- m1 = ms
        m2 = M.findWithDefault M.empty ("Class", iri) m1
        axioms = M.findWithDefault [] "subClassOf" m2
        newAxioms = S.toList . S.fromList $ ClassAxiom clAx : axioms

-- EquivalentClasses axiom
tClassAxiom clAx@(EquivalentClasses anns
    [Expression iri1, Expression iri2]) ms =
    M.insert ("Class", iri1) (M.insert "equivalentTo" newAxioms1 m1)
    . M.insert ("Class", iri2) (M.insert "equivalentTo" newAxioms2 m2) $ m'
    where
        m' = tAnnotations anns ms
        m1 = M.findWithDefault M.empty ("Class", iri1) m'
        m2 = M.findWithDefault M.empty ("Class", iri2) m'
        axioms1 = M.findWithDefault [] "equivalentTo" m1
        axioms2 = M.findWithDefault [] "equivalentTo" m2
        newAxioms1 = S.toList . S.fromList $ ClassAxiom clAx : axioms1
        newAxioms2 = S.toList . S.fromList
            $ (ClassAxiom . EquivalentClasses anns $
                [Expression iri2, Expression iri1]) : axioms2

tClassAxiom clAx@(EquivalentClasses anns [Expression iri, clExpr]) ms =
    M.insert ("Class", iri) (M.insert "equivalentTo" newAxioms m1) $ m'
    where
        m' = tAnnotations anns . tClassExpression clExpr $ ms
        m1 = M.findWithDefault M.empty ("Class", iri) m'
        axioms = M.findWithDefault [] "equivalentTo" m1
        newAxioms = S.toList . S.fromList $ ClassAxiom clAx : axioms

tClassAxiom clAx@(EquivalentClasses anns clExprs) ms =
    M.insert ("Misc", nullIRI) (M.insert "equivalentClasses" newAxioms m1) $ m'
    where
        m' = tAnnotations anns . tClassExpressions clExprs $ ms
        m1 = M.findWithDefault M.empty ("Misc", nullIRI) m'
        axioms = M.findWithDefault [] "equivalentClasses" m1
        newAxioms = S.toList . S.fromList $ ClassAxiom clAx : axioms

-- | transform Annotations
tAnnotations :: [Annotation] -> MnchstrSntx -> MnchstrSntx
tAnnotations = flip $ foldr tAnnotation

tAnnotation :: Annotation -> MnchstrSntx -> MnchstrSntx
tAnnotation (Annotation anns annProp annVal) ms =
    M.insert k (M.findWithDefault M.empty k m1) m1
    where
        k = ("AnnotationProperty", annProp)
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
    where k = ("Class", iri)

tClassExpression (ObjectJunction _ clExprs) ms = tClassExpressions clExprs ms

tClassExpression (ObjectComplementOf clExpr) ms = tClassExpression clExpr ms

tClassExpression (ObjectOneOf inds) ms = tIndividuals inds ms

tClassExpression (ObjectValuesFrom _ obPropExpr clExpr) ms =
    tObjectPropertyExpression obPropExpr
    . tClassExpression clExpr $ ms

tClassExpression (ObjectHasValue obPropExpr ind) ms =
    tObjectPropertyExpression obPropExpr
    . tIndividual ind $ ms

tClassExpression (ObjectHasSelf obPropExpr) ms = 
    tObjectPropertyExpression obPropExpr ms

tClassExpression (ObjectCardinality card) ms =
    case card of
        Cardinality ct n obPropExpr (Just clExpr) ->
            tObjectPropertyExpression obPropExpr
            . tClassExpression clExpr $ ms
        Cardinality ct n obPropExpr Nothing ->
            tObjectPropertyExpression obPropExpr ms

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
tObjectPropertyExpression :: ObjectPropertyExpression
    -> MnchstrSntx -> MnchstrSntx
tObjectPropertyExpression (ObjectProp iri) ms =
    M.insert k (M.findWithDefault M.empty k ms) ms
    where k = ("ObjectProperty", iri)

tObjectPropertyExpression (ObjectInverseOf ope) ms =
    tObjectPropertyExpression ope ms

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
    where k = ("Datatype", iri)

-- | transform Literal
tLiteral :: Literal -> MnchstrSntx -> MnchstrSntx
tLiteral (Literal _ t) ms = case t of
    Typed dt -> tDatatype dt ms
    Untyped _ ->  tDatatype (setPrefix "xsd" . mkIRI $ "PlainLiteral") ms

-- | transform DataPropertyExpression
tDataPropertyExpression :: DataPropertyExpression
    -> MnchstrSntx -> MnchstrSntx
tDataPropertyExpression iri ms =
    M.insert k (M.findWithDefault M.empty k ms) ms
    where k = ("DataProperty", iri)

-- | transform Individual
tIndividuals :: [Individual] -> MnchstrSntx -> MnchstrSntx
tIndividuals = flip $ foldr tIndividual

tIndividual :: Individual -> MnchstrSntx -> MnchstrSntx
tIndividual iri ms =
    M.insert k (M.findWithDefault M.empty k ms) ms
    where k = ("Individual", iri)
    
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
    tabs n <> keyword "ObjectProperty:" <+> printIRI pds (snd header)

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
    tabs n <> keyword "DataProperty:" <+> printIRI pds (snd header)

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
    tabs n <> keyword "AnnotationProperty:" <+> printIRI pds (snd header)

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
    tabs n <> keyword "Datatype:" <+> printMSDatatype pds (snd header)

printMSDatatype :: [PrefixDeclaration] -> IRI -> Doc
printMSDatatype pds iri
    | isAbbrev iri && prefixName iri == "xsd" =
        if iFragment iri `elem` ["integer", "decimal", "float", "string"]
        then text . iFragment $ iri
        else printIRI pds iri
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
    vcat [tabs n <> keyword "Class:" <+> printIRI pds (snd header)
        , scoDocs, eqDocs]
    where
        -- annAxioms = M.findWithDefault [] "annotation" body
        scoAxioms = M.findWithDefault [] "subClassOf" body
        scoDocs = axiomsToDoc pds (n + 1) "SubClassOf:" scoAxioms

        eqAxioms = M.findWithDefault [] "equivalentTo" body
        eqDocs = axiomsToDoc pds (n + 1) "EquivalentTo:" eqAxioms


axiomsToDoc :: [PrefixDeclaration] -> Int -> String -> [Axiom] -> Doc
axiomsToDoc pds n header axioms = case axioms of
    [] -> empty
    _ ->  tabs n <> keyword header
        $+$ (printClassAxiomsVer pds (n + 1)
            . map unpackClassAxiom
            $ axioms)

unpackClassAxiom :: Axiom -> ClassAxiom
unpackClassAxiom (ClassAxiom a) = a

-- | print ClassAxioms
printClassAxiomsHor :: [PrefixDeclaration] -> Int -> [ClassAxiom] -> Doc
printClassAxiomsHor pds n axioms =
    tabs n <> (hsep . punctuate comma . map (printClassAxiom pds 0) $ axioms)

printClassAxiomsVer :: [PrefixDeclaration] -> Int -> [ClassAxiom] -> Doc
printClassAxiomsVer pds n =
    vcat . punctuate comma . map (printClassAxiom pds n)

printClassAxiom :: [PrefixDeclaration] -> Int -> ClassAxiom -> Doc
printClassAxiom pds n (SubClassOf anns iri supClExpr) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printClassExpression pds supClExpr

printClassAxiom pds n (EquivalentClasses anns [_, clExpr]) =
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printClassExpression pds clExpr

printClassAxiom pds n (EquivalentClasses anns clExprs) = 
    printAnnotations pds (n + 1) anns
    $+$
    tabs n <> printClassExpressionsHor pds clExprs

-- | print Individual Frames
printIFs :: [PrefixDeclaration] -> Int -> MnchstrSntx -> Doc
printIFs pds n ms = empty

-- | print Individual Frame
printIF :: [PrefixDeclaration] -> Int -> FrameId
    -> M.Map String [Axiom] -> Doc
printIF pds n header body = empty 

-- | print Misc Frame
printMF :: [PrefixDeclaration] -> Int -> MnchstrSntx -> Doc
printMF pds n ms
    | M.null mRoot = empty
    | otherwise = 
        vcat [eqDocs]
    where
        mRoot = M.findWithDefault M.empty ("Misc", nullIRI) ms
        eqAxioms = M.findWithDefault [] "equivalentClasses" mRoot
        eqDocs = eqMFAxiomsToDoc pds n eqAxioms

eqMFAxiomsToDoc :: [PrefixDeclaration] -> Int -> [Axiom] -> Doc
eqMFAxiomsToDoc pds n [] = empty
eqMFAxiomsToDoc pds n axioms =
    vsep docsWithHeaders
    where
        classAxioms = map unpackClassAxiom axioms
        bodyDocs = map (printClassAxiom pds (n + 1)) classAxioms
        docsWithHeaders = map (\d -> keyword "EquivalentClases:" $+$ d) bodyDocs

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
printLiteral pds lit = case lit of 
    Literal lexi ty -> plainText ('"' : escapeString lexi ++ "\"")
        <> literalTail ty
    NumberLit f -> text (show f)
    where 
        literalTail ty = case ty of
            Typed iri -> keyword cTypeS <> printDataIRI pds iri
            Untyped tag -> case tag of
                Nothing -> empty
                Just tg -> text asP <> text tg

escapeString ::  String -> String
escapeString [] = []
escapeString ('"':s) = '\\' : '"' : escapeString s
escapeString ('\\':s) = '\\' : '\\' : escapeString s
escapeString (c:s) = c : escapeString s 

---------------- | print ObjectPropertyExpression
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
        && (iFragment f) `elem` ["length", "minLength", "maxLength", "pattern"] =
            iFragment f
    | isAbbrev f && prefixName f == "rdf" && iFragment f == "langRange" =
        "langRange"
    | isAbbrev f && prefixName f == "xsd" && iFragment f == "minInclusive" =
        "<="
    | isAbbrev f && prefixName f == "xsd" && iFragment f == "minExclusive" =
        "<"
    | isAbbrev f && prefixName f == "xsd" && iFragment f == "maxInclusive" =
        ">="
    | isAbbrev f && prefixName f == "xsd" && iFragment f == "maxExclusive" =
        ">"
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
        <+> maybe (keyword "Thing") (printPrimary pds) maybeDesc
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

