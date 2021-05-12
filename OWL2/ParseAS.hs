{-# LANGUAGE TupleSections #-}

module OWL2.ParseAS where

import OWL2.AS

import Common.AnnoParser (newlineOrEof)
import Common.IRI hiding (parseIRI)
import Common.Parsec
import Common.Lexer (getNumber, value)

import Text.ParserCombinators.Parsec

import Data.Char

{- | @p <|?> q@ behaves like @<|>@ but pretends it hasn't consumed any input
when an options failes. -}
(<|?>) :: (GenParser t st a ) -> (GenParser t st a) -> GenParser t st a
p <|?> q = try p <|> try q
infixr 1 <|?>

{- | @manySkip p@ parses 0 or more occurences of @p@ while skipping spaces
(and comments) inbetween -}
manySkip :: CharParser st a -> CharParser st [a]
manySkip p = many (p << skips)

{- | @many1Skip p@ parses 1 or more occurences of @p@ while skipping spaces
(and comments) inbetween -}
many1Skip :: CharParser st a -> CharParser st [a]
many1Skip p = many1 (p << skips)

{- | @manyNSkip n p@ parses @n@ or more occurences of @p@ while skipping spaces
(and comments) inbetween -}
manyNSkip :: Int -> CharParser st a -> CharParser st [a]
manyNSkip n p =
    foldr (\ _ r -> (p << skips) <:> r) (return []) [1 .. n] <++>
    many (p << skips)

{- | @followedBy c p@ first parses @p@ then looks ahead for @c@. Doesn't consume
any input on failure. -}
followedBy :: CharParser st b -> CharParser st a -> CharParser st a
followedBy cond p = try $ do
    r <- p
    lookAhead cond
    return r

-- | Performs an arbitrary lookahead over choices of parsers
arbitraryLookaheadOption :: [CharParser st a] -> CharParser st a
arbitraryLookaheadOption p = lookAhead $ choice (try <$> p)

-- | alias for @return Nothing@
never :: CharParser st (Maybe a)
never = return Nothing

-- # Basic constructs

-- | Parses a comment
comment :: CharParser st String
comment = try $ do
    char '#'
    manyTill anyChar newlineOrEof

-- | Skips whitespaces and comments
skips :: CharParser st ()
skips = skipMany (forget space <|> forget comment <?> "")

-- | Skips whitespaces and comments preceeding a given parser
skipsp :: CharParser st a -> CharParser st a
skipsp d = skips >> d



-- | Parses plain string with skip
keyword :: String -> CharParser st ()
keyword s = do
    skipsp $ try (string s >> notFollowedBy alphaNum)

-- | Parses a full iri
fullIri :: CharParser st IRI
fullIri = angles iriParser

ncNameStart :: Char -> Bool
ncNameStart c = isAlpha c || c == '_'

-- | rfc3987 plus '+' from scheme (scheme does not allow the dots)
ncNameChar :: Char -> Bool
ncNameChar c = isAlphaNum c || elem c ".+-_\183"

-- | Parses a prefix name (PNAME_NS of SPARQL)
prefix :: CharParser st String
prefix = option "" (satisfy ncNameStart <:> many (satisfy ncNameChar))
    <++> string ":"

-- | Parses an abbreviated or full iri
parseIRI :: CharParser st IRI
parseIRI = fullIri <|?> compoundIriCurie <?> "IRI"


{- | @parseEnclosedWithKeyword k p@ parses the keyword @k@ followed @p@
enclosed in parentheses. Skips spaces and comments before and after @p@. -}
parseEnclosedWithKeyword :: String -> CharParser st a -> CharParser st a
parseEnclosedWithKeyword s p = do
    keyword s
    skips
    char '('
    skips
    r <- p
    skips
    char ')'
    return r

parsePrefixDeclaration :: CharParser st PrefixDeclaration
parsePrefixDeclaration = parseEnclosedWithKeyword "Prefix" $ do
    p <- prefix
    skips
    char '='
    skips
    iri <- fullIri
    return $ PrefixDeclaration p iri

parseDirectlyImportsDocument :: CharParser st IRI
parseDirectlyImportsDocument = parseEnclosedWithKeyword "Import" parseIRI <?>
    "Import"

-- # Entities, Literals, and Individuals

-- ## Entities
parseEntity' :: EntityType -> String -> CharParser st Entity
parseEntity' t k = parseEnclosedWithKeyword k $ do
    iri <- skipsp parseIRI
    return $ mkEntity t iri

parseEntity :: CharParser st Entity
parseEntity =
    parseEntity' Class "Class" <|?>
    parseEntity' Datatype "Datatype" <|?>
    parseEntity' ObjectProperty "ObjectProperty" <|?>
    parseEntity' DataProperty "DataProperty" <|?>
    parseEntity' AnnotationProperty "AnnotationProperty" <|?>
    parseEntity' NamedIndividual "NamedIndividual" <?>
    "Entity"

-- ## Literals


charOrEscaped :: CharParser st Char
charOrEscaped = try (string "\\\"" >> return '"')
            <|> try (string "\\\\" >> return '\\') <|> anyChar

parseTypedLiteral :: CharParser st Literal
parseTypedLiteral = do
    char '"'
    s <- manyTill charOrEscaped (try $ char '"')
    string "^^"
    iri <- parseIRI
    return $ Literal s (Typed iri)

parseLanguageTag :: CharParser st String
parseLanguageTag = do
    char '@'
    many1 (letter <|?> char '-')

parseUntypedLiteral :: CharParser st Literal
parseUntypedLiteral = do
    char '"'
    s <- manyTill charOrEscaped (try $ char '"')
    languageTag <- optionMaybe (try parseLanguageTag)
    return $ Literal s (Untyped languageTag)

parseLiteral :: CharParser st Literal
parseLiteral = skipsp (parseTypedLiteral <|?> parseUntypedLiteral) <?> "Literal"

-- ## Individuals

parseAnonymousIndividual :: CharParser st AnonymousIndividual
parseAnonymousIndividual = iriCurie


parseIndividual :: CharParser st Individual
parseIndividual = skipsp parseIRI <|?> skipsp parseAnonymousIndividual <?>
    "Individual"

-- # Annotations
parseAnnotationValue :: CharParser st AnnotationValue
parseAnnotationValue =
     (parseLiteral >>= return . AnnValLit) <|?>
     (skipsp parseIRI >>= return . AnnValue) <|?>
     (skipsp parseAnonymousIndividual >>= return . AnnAnInd) <?>
     "AnnotationValue"

parseAnnotationSubject :: CharParser st AnnotationSubject
parseAnnotationSubject = 
    (AnnSubAnInd <$> skipsp parseAnonymousIndividual) <|?>
    (AnnSubIri <$> skipsp parseIRI)

parseAnnotations :: CharParser st [Annotation]
parseAnnotations = manySkip parseAnnotation

parseAnnotation :: CharParser st Annotation
parseAnnotation = (flip (<?>)) "Annotation" $
    parseEnclosedWithKeyword "Annotation" $ do
        an <- (manySkip (try parseAnnotation))
        skips
        property <- parseIRI
        skips
        v <- parseAnnotationValue
        return $ Annotation an property v

parseIriIfNotImportOrAxiomOrAnnotation :: CharParser st (Maybe IRI)
parseIriIfNotImportOrAxiomOrAnnotation =
    (arbitraryLookaheadOption [
        forget parseDirectlyImportsDocument,
        forget parseAnnotation,
        forget parseAxiom
    ] >> never) <|>
    optionMaybe parseIRI


-- ## Data Range

parseDataJunction' :: String -> JunctionType -> CharParser st DataRange
parseDataJunction' k t = parseEnclosedWithKeyword k $
    DataJunction t <$> manyNSkip 2 parseDataRange

parseDataJunction :: CharParser st DataRange
parseDataJunction =
    parseDataJunction' "DataUnionOf" UnionOf <|?>
    parseDataJunction' "DataIntersectionOf" IntersectionOf

parseDataComplementOf :: CharParser st DataRange
parseDataComplementOf = parseEnclosedWithKeyword "DataComplementOf" $
    DataComplementOf <$> parseDataRange

parseDataOneOf :: CharParser st DataRange
parseDataOneOf = parseEnclosedWithKeyword "DataOneOf" $
    DataOneOf <$> many1Skip parseLiteral

parseDatatypeResComponent :: CharParser st (ConstrainingFacet, RestrictionValue)
parseDatatypeResComponent =
    (,) <$>
    skipsp parseIRI <*>
    parseLiteral

parseDatatypeRestriction :: CharParser st DataRange
parseDatatypeRestriction = parseEnclosedWithKeyword "DatatypeRestriction" $ do
    dataType <- parseIRI
    skips
    restrictions <- many1Skip parseDatatypeResComponent
    return $ DataType dataType restrictions

parseDataRange :: CharParser st DataRange
parseDataRange =
    parseDataJunction <|?>
    parseDataComplementOf <|?>
    parseDataOneOf <|?>
    parseDatatypeRestriction <|?>
    (DataType <$> skipsp parseIRI <*> return []) <?>
    "DataRange"

{- # Axioms

## Declaration -}

parseDeclaration :: CharParser st Axiom
parseDeclaration = parseEnclosedWithKeyword "Declaration" $ do
    annotations <- manySkip parseAnnotation
    skips
    entity <- parseEntity
    return $ Declaration annotations entity

-- ## ClassExpressions

parseObjectIntersectionOf :: CharParser st ClassExpression
parseObjectIntersectionOf = parseEnclosedWithKeyword "ObjectIntersectionOf" $
    ObjectJunction IntersectionOf <$> manyNSkip 2 parseClassExpression

parseObjectUnionOf :: CharParser st ClassExpression
parseObjectUnionOf = parseEnclosedWithKeyword "ObjectUnionOf" $
    ObjectJunction UnionOf <$> manyNSkip 2 parseClassExpression

parseObjectComplementOf :: CharParser st ClassExpression
parseObjectComplementOf = parseEnclosedWithKeyword "ObjectComplementOf" $
    ObjectComplementOf <$> parseClassExpression

parseObjectOneOf :: CharParser st ClassExpression
parseObjectOneOf = parseEnclosedWithKeyword "ObjectOneOf" $
    ObjectOneOf <$> many1Skip parseIndividual

parseObjectProperty :: CharParser st ObjectPropertyExpression
parseObjectProperty = ObjectProp <$> skipsp parseIRI

parseInverseObjectProperty :: CharParser st ObjectPropertyExpression
parseInverseObjectProperty = parseEnclosedWithKeyword "ObjectInverseOf" $
    ObjectInverseOf <$> parseObjectProperty

parseObjectPropertyExpression :: CharParser st ObjectPropertyExpression
parseObjectPropertyExpression =
    parseInverseObjectProperty <|?>
    parseObjectProperty <?>
    "ObjectPropertyExpression"


parseObjectSomeValuesFrom :: CharParser st ClassExpression
parseObjectSomeValuesFrom = parseEnclosedWithKeyword "ObjectSomeValuesFrom" $ do
    objectPropertyExpr <- parseObjectPropertyExpression
    skips
    classExpr <- parseClassExpression
    return $ ObjectValuesFrom SomeValuesFrom objectPropertyExpr classExpr

parseObjectAllValuesFrom :: CharParser st ClassExpression
parseObjectAllValuesFrom = parseEnclosedWithKeyword "ObjectAllValuesFrom" $ do
    objectPropertyExpr <- parseObjectPropertyExpression
    skips
    classExpr <- parseClassExpression
    return $ ObjectValuesFrom AllValuesFrom objectPropertyExpr classExpr

parseObjectHasValue :: CharParser st ClassExpression
parseObjectHasValue = parseEnclosedWithKeyword "ObjectHasValue" $ do
    objectPropertyExpr <- parseObjectPropertyExpression
    skips
    val <- parseIndividual
    return $ ObjectHasValue objectPropertyExpr val

parseObjectHasSelf :: CharParser st ClassExpression
parseObjectHasSelf = parseEnclosedWithKeyword "ObjectHasSelf" $
    ObjectHasSelf <$> parseObjectPropertyExpression

parseCardinality' :: CardinalityType
                     -> String
                     -> CharParser st a
                     -> CharParser st b
                     -> CharParser st (Cardinality a b)
parseCardinality' c k pa pb = parseEnclosedWithKeyword k $ do
    n <- value 10 <$> getNumber
    skips
    objectPropertyExpr <- pa
    skips
    classExpr <- optionMaybe (pb << skips)
    return $ Cardinality c n objectPropertyExpr classExpr

parseObjectCardinality :: CharParser st ClassExpression
parseObjectCardinality = ObjectCardinality <$> (
        cardinality "ObjectMinCardinality" MinCardinality <|?>
        cardinality "ObjectMaxCardinality" MaxCardinality <|?>
        cardinality "ObjectExactCardinality" ExactCardinality
    )
    where cardinality s t = (parseCardinality' t s a b)
          a = parseObjectPropertyExpression
          b = parseClassExpression

parseDataCardinality :: CharParser st ClassExpression
parseDataCardinality = DataCardinality <$> (
        cardinality "DataMinCardinality" MinCardinality <|?>
        cardinality "DataMaxCardinality" MaxCardinality <|?>
        cardinality "DataExactCardinality" ExactCardinality
    )
    where cardinality s t = (parseCardinality' t s a b)
          a = parseIRI
          b = parseDataRange


parseDataSomeValuesFrom :: CharParser st ClassExpression
parseDataSomeValuesFrom = parseEnclosedWithKeyword "DataSomeValuesFrom" $ do
    exprs <- many1 (followedBy (skipsp parseDataRange) (skipsp parseIRI))
    skips
    range <- parseDataRange
    return $ DataValuesFrom SomeValuesFrom exprs range

parseDataAllValuesFrom :: CharParser st ClassExpression
parseDataAllValuesFrom = parseEnclosedWithKeyword "DataAllValuesFrom" $ do
    exprs <- many1 (followedBy parseDataRange (skipsp parseIRI))
    skips
    range <- parseDataRange
    return $ DataValuesFrom AllValuesFrom exprs range

parseDataHasValue :: CharParser st ClassExpression
parseDataHasValue = parseEnclosedWithKeyword "DataHasValue" $
    DataHasValue <$> skipsp parseIRI <*> parseLiteral


parseClassExpression :: CharParser st ClassExpression
parseClassExpression =
    parseObjectIntersectionOf <|?>
    parseObjectUnionOf <|?>
    parseObjectComplementOf <|?>
    parseObjectOneOf <|?>
    parseObjectCardinality <|?>
    parseObjectSomeValuesFrom <|?>
    parseObjectAllValuesFrom <|?>
    parseObjectHasValue <|?>
    parseObjectHasSelf <|?>
    parseDataSomeValuesFrom <|?>
    parseDataAllValuesFrom <|?>
    parseDataHasValue <|?>
    parseDataCardinality <|?>
    (Expression <$> skipsp parseIRI) <?>
    "ClassExpression"

-- ## Class Axioms

parseSubClassOf :: CharParser st ClassAxiom
parseSubClassOf = parseEnclosedWithKeyword "SubClassOf" $ do
    annotations <- manySkip parseAnnotation
    skips
    subClassExpression <- parseClassExpression
    skips
    superClassExpression <- parseClassExpression
    return $ SubClassOf annotations subClassExpression superClassExpression

parseEquivalentClasses :: CharParser st ClassAxiom
parseEquivalentClasses = parseEnclosedWithKeyword "EquivalentClasses" $
    EquivalentClasses <$> parseAnnotations <*> manyNSkip 2 parseClassExpression

parseDisjointClasses :: CharParser st ClassAxiom
parseDisjointClasses = parseEnclosedWithKeyword "DisjointClasses" $
    DisjointClasses <$> parseAnnotations <*> manyNSkip 2 parseClassExpression

parseDisjointUnion :: CharParser st ClassAxiom
parseDisjointUnion = parseEnclosedWithKeyword "DisjointUnion" $
    DisjointUnion <$>
    parseAnnotations <*>
    skipsp parseIRI <*>
    manyNSkip 2 parseClassExpression

parseClassAxiom :: CharParser st Axiom
parseClassAxiom = ClassAxiom <$> (
        parseSubClassOf <|?>
        parseEquivalentClasses <|?>
        parseDisjointClasses <|?>
        parseDisjointUnion <?> "ClassAxiom"
    )

-- ## Object Property Axioms

parseEquivalentObjectProperties :: CharParser st ObjectPropertyAxiom
parseEquivalentObjectProperties =
    parseEnclosedWithKeyword "EquivalentObjectProperties" $
    EquivalentObjectProperties <$>
    parseAnnotations <*>
    manyNSkip 2 parseObjectPropertyExpression

parseDisjointObjectProperties :: CharParser st ObjectPropertyAxiom
parseDisjointObjectProperties =
    parseEnclosedWithKeyword "DisjointObjectProperties" $
    DisjointObjectProperties <$>
    parseAnnotations <*>
    manyNSkip 2 parseObjectPropertyExpression

parseObjectPropertyDomain :: CharParser st ObjectPropertyAxiom
parseObjectPropertyDomain =
    parseEnclosedWithKeyword "ObjectPropertyDomain" $
    ObjectPropertyDomain <$>
    parseAnnotations <*>
    parseObjectPropertyExpression <*>
    parseClassExpression

parseObjectPropertyRange :: CharParser st ObjectPropertyAxiom
parseObjectPropertyRange =
    parseEnclosedWithKeyword "ObjectPropertyRange" $
    ObjectPropertyRange <$>
    parseAnnotations <*>
    parseObjectPropertyExpression <*>
    parseClassExpression

parseInverseObjectProperties :: CharParser st ObjectPropertyAxiom
parseInverseObjectProperties =
    parseEnclosedWithKeyword "InverseObjectProperties" $
    InverseObjectProperties <$>
    parseAnnotations <*>
    parseObjectPropertyExpression <*>
    parseObjectPropertyExpression


-- ### SubObjectPropertyOf
parseObjectPropertyExpressionChain :: CharParser st PropertyExpressionChain
parseObjectPropertyExpressionChain =
    parseEnclosedWithKeyword "ObjectPropertyChain" $
    manyNSkip 2 parseObjectPropertyExpression

parseSubObjectPropertyExpression :: CharParser st SubObjectPropertyExpression
parseSubObjectPropertyExpression =
    SubObjPropExpr_exprchain <$> parseObjectPropertyExpressionChain <|?>
    SubObjPropExpr_obj <$> parseObjectPropertyExpression <?>
    "SubObjectPropertyExpression"

parseSubObjectPropertyOf :: CharParser st ObjectPropertyAxiom
parseSubObjectPropertyOf = parseEnclosedWithKeyword "SubObjectPropertyOf" $
    SubObjectPropertyOf <$>
    parseAnnotations <*>
    parseSubObjectPropertyExpression <*>
    parseObjectPropertyExpression


-- | Helper function for *C*ommon*O*bject*P*roperty*A*xioms
parseCOPA :: (
        AxiomAnnotations -> ObjectPropertyExpression -> ObjectPropertyAxiom
    ) -> String -> CharParser st ObjectPropertyAxiom
parseCOPA c s = parseEnclosedWithKeyword s $
    c <$>
    parseAnnotations <*>
    parseObjectPropertyExpression

parseObjectPropertyAxiom :: CharParser st Axiom
parseObjectPropertyAxiom = ObjectPropertyAxiom <$> (
        parseSubObjectPropertyOf <|?>
        parseEquivalentObjectProperties <|?>
        parseDisjointObjectProperties <|?>
        parseObjectPropertyDomain <|?>
        parseObjectPropertyRange <|?>
        parseInverseObjectProperties <|?>
        parseCOPA FunctionalObjectProperty "FunctionalObjectProperty" <|?>
        parseCOPA InverseFunctionalObjectProperty
            "InverseFunctionalObjectProperty" <|?>
        parseCOPA ReflexiveObjectProperty "ReflexiveObjectProperty" <|?>
        parseCOPA IrreflexiveObjectProperty "IrreflexiveObjectProperty" <|?>
        parseCOPA SymmetricObjectProperty "SymmetricObjectProperty" <|?>
        parseCOPA AsymmetricObjectProperty "AsymmetricObjectProperty" <|?>
        parseCOPA TransitiveObjectProperty "TransitiveObjectProperty" <?>
        "ObjectPropertyAxiom"
    )

-- ## DataPropertyAxioms

parseSubDataPropertyOf :: CharParser st DataPropertyAxiom
parseSubDataPropertyOf = parseEnclosedWithKeyword "SubDataPropertyOf" $
    SubDataPropertyOf <$>
    parseAnnotations <*>
    skipsp parseIRI <*>
    skipsp parseIRI

parseEquivalentDataProperties :: CharParser st DataPropertyAxiom
parseEquivalentDataProperties =
    parseEnclosedWithKeyword "EquivalentDataProperties" $
    EquivalentDataProperties <$>
    parseAnnotations <*>
    manyNSkip 2 parseIRI

parseDisjointDataProperties :: CharParser st DataPropertyAxiom
parseDisjointDataProperties =
    parseEnclosedWithKeyword "DisjointDataProperties" $
    DisjointDataProperties <$>
    parseAnnotations <*>
    manyNSkip 2 parseIRI

parseDataPropertyDomain :: CharParser st DataPropertyAxiom
parseDataPropertyDomain =
    parseEnclosedWithKeyword "DataPropertyDomain" $
    DataPropertyDomain <$>
    parseAnnotations <*>
    skipsp parseIRI <*>
    parseClassExpression

parseDataPropertyRange :: CharParser st DataPropertyAxiom
parseDataPropertyRange =
    parseEnclosedWithKeyword "DataPropertyRange" $
    DataPropertyRange <$>
    parseAnnotations <*>
    skipsp parseIRI <*>
    parseDataRange

parseFunctionalDataProperty :: CharParser st DataPropertyAxiom
parseFunctionalDataProperty =
    parseEnclosedWithKeyword "FunctionalDataProperty" $
    FunctionalDataProperty <$>
    parseAnnotations <*>
    skipsp parseIRI

parseDataPropertyAxiom :: CharParser st Axiom
parseDataPropertyAxiom = DataPropertyAxiom <$> (
        parseSubDataPropertyOf <|?>
        parseEquivalentDataProperties <|?>
        parseDisjointDataProperties <|?>
        parseDataPropertyDomain <|?>
        parseDataPropertyRange <|?>
        parseFunctionalDataProperty <?>
        "DataPropertyAxiom"
    )

-- ## Data Type Definition
parseDataTypeDefinition :: CharParser st Axiom
parseDataTypeDefinition = parseEnclosedWithKeyword "DatatypeDefinition" $
    DatatypeDefinition <$>
    parseAnnotations <*>
    skipsp parseIRI <*>
    parseDataRange

-- ## HasKey
parseHasKey :: CharParser st Axiom
parseHasKey = parseEnclosedWithKeyword "HasKey" $ do
    annotations <- parseAnnotations
    skips
    classExpr <- parseClassExpression
    skips
    char '('
    skips
    objectPropertyExprs <- manySkip parseObjectPropertyExpression
    skips
    char ')'
    skips
    char '('
    skips
    dataPropertyExprs <- manySkip parseIRI
    skips
    char ')'
    return $ HasKey annotations classExpr objectPropertyExprs dataPropertyExprs

-- ## Assertion
parseSameIndividual :: CharParser st Assertion
parseSameIndividual = parseEnclosedWithKeyword "SameIndividual" $
    SameIndividual <$>
    parseAnnotations <*>
    manyNSkip 2 parseIndividual

parseDifferentIndividuals :: CharParser st Assertion
parseDifferentIndividuals = parseEnclosedWithKeyword "DifferentIndividuals" $
    DifferentIndividuals <$>
    parseAnnotations <*>
    manyNSkip 2 parseIndividual

parseClassAssertion :: CharParser st Assertion
parseClassAssertion = parseEnclosedWithKeyword "ClassAssertion" $
    ClassAssertion <$>
    parseAnnotations <*>
    parseClassExpression <*>
    parseIndividual

parseObjectPropertyAssertion :: CharParser st Assertion
parseObjectPropertyAssertion =
    parseEnclosedWithKeyword "ObjectPropertyAssertion" $
    ObjectPropertyAssertion <$>
    parseAnnotations <*>
    parseObjectPropertyExpression <*>
    parseIndividual <*>
    parseIndividual

parseNegativeObjectPropertyAssertion :: CharParser st Assertion
parseNegativeObjectPropertyAssertion =
    parseEnclosedWithKeyword "NegativeObjectPropertyAssertion" $
    NegativeObjectPropertyAssertion <$>
    parseAnnotations <*>
    parseObjectPropertyExpression <*>
    parseIndividual <*>
    parseIndividual

parseDataPropertyAssertion :: CharParser st Assertion
parseDataPropertyAssertion =
    parseEnclosedWithKeyword "DataPropertyAssertion" $
    DataPropertyAssertion <$>
    parseAnnotations <*>
    skipsp parseIRI <*>
    parseIndividual <*>
    parseLiteral

parseNegativeDataPropertyAssertion :: CharParser st Assertion
parseNegativeDataPropertyAssertion =
    parseEnclosedWithKeyword "NegativeDataPropertyAssertion" $
    NegativeDataPropertyAssertion <$>
    parseAnnotations <*>
    skipsp parseIRI <*>
    parseIndividual <*>
    parseLiteral

parseAssertion :: CharParser st Axiom
parseAssertion = Assertion <$> (
        parseSameIndividual <|?>
        parseDifferentIndividuals <|?>
        parseClassAssertion <|?>
        parseObjectPropertyAssertion <|?>
        parseNegativeObjectPropertyAssertion <|?>
        parseDataPropertyAssertion <|?>
        parseNegativeDataPropertyAssertion
    )


parseAnnotationAssertion :: CharParser st AnnotationAxiom
parseAnnotationAssertion = parseEnclosedWithKeyword "AnnotationAssertion" $
    AnnotationAssertion <$>
    parseAnnotations <*>
    skipsp parseIRI <*>
    parseAnnotationSubject <*>
    parseAnnotationValue

parseSubAnnotationPropertyOf :: CharParser st AnnotationAxiom
parseSubAnnotationPropertyOf = 
    parseEnclosedWithKeyword "SubAnnotationPropertyOf" $
    SubAnnotationPropertyOf <$>
    parseAnnotations <*>
    skipsp parseIRI <*>
    skipsp parseIRI

parseAnnotationPropertyDomain :: CharParser st AnnotationAxiom
parseAnnotationPropertyDomain =
    parseEnclosedWithKeyword "AnnotationPropertyDomain" $
    AnnotationPropertyDomain <$>
    parseAnnotations <*>
    skipsp parseIRI <*>
    skipsp parseIRI

parseAnnotationPropertyRange :: CharParser st AnnotationAxiom
parseAnnotationPropertyRange =
    parseEnclosedWithKeyword "AnnotationPropertyRange" $
    AnnotationPropertyRange <$>
    parseAnnotations <*>
    skipsp parseIRI <*>
    skipsp parseIRI

parseAnnotationAxiom :: CharParser st Axiom
parseAnnotationAxiom = AnnotationAxiom <$> (
        parseAnnotationAssertion <|?>
        parseSubAnnotationPropertyOf <|?>
        parseAnnotationPropertyDomain <|?>
        parseAnnotationPropertyRange
    )

parseAxiom :: CharParser st Axiom
parseAxiom =
    parseDeclaration <|?>
    parseClassAxiom <|?>
    parseObjectPropertyAxiom <|?>
    parseDataPropertyAxiom <|?>
    parseDataTypeDefinition <|?>
    parseHasKey <|?>
    parseAssertion <|?>
    parseAnnotationAxiom <?>
    "Axiom"


parseOntology :: CharParser st Ontology
parseOntology = parseEnclosedWithKeyword "Ontology" $ do
    ontologyIri <- parseIriIfNotImportOrAxiomOrAnnotation
    skips
    versionIri <- parseIriIfNotImportOrAxiomOrAnnotation
    skips
    imports <- manySkip parseDirectlyImportsDocument
    skips
    annotations <- manySkip parseAnnotation
    skips
    axioms <- manySkip parseAxiom
    return $ Ontology ontologyIri versionIri (imports) annotations axioms


-- | Parses an OntologyDocument from Owl2 Functional Syntax
parseOntologyDocument :: CharParser st OntologyDocument
parseOntologyDocument =
    OntologyDocument <$>
    manySkip parsePrefixDeclaration <*>
    (skipsp parseOntology)
