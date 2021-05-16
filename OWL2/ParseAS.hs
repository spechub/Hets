{-# LANGUAGE TupleSections #-}

module OWL2.ParseAS where

import OWL2.AS

import Common.AnnoParser (newlineOrEof)
import Common.IRI hiding (parseIRI)
import Common.Parsec
import Common.Lexer (getNumber, value)
import qualified Common.GlobalAnnotations as GA (PrefixMap)

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
parseIRI :: GA.PrefixMap -> CharParser st IRI
parseIRI pm =fullIri <|?> compoundIriCurie <?> "IRI"


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

parsePrefixDeclaration :: GA.PrefixMap -> CharParser st PrefixDeclaration
parsePrefixDeclaration pm =parseEnclosedWithKeyword "Prefix" $ do
    p <- prefix
    skips
    char '='
    skips
    iri <- fullIri
    return $ PrefixDeclaration p iri

parseDirectlyImportsDocument :: GA.PrefixMap -> CharParser st IRI
parseDirectlyImportsDocument pm =parseEnclosedWithKeyword "Import" parseIRI <?>
    "Import"

-- # Entities, Literals, and Individuals

-- ## Entities
parseEntity' :: EntityType -> String -> CharParser st Entity
parseEntity' t k = parseEnclosedWithKeyword k $ do
    iri <- skipsp parseIRI
    return $ mkEntity t iri

parseEntity :: GA.PrefixMap -> CharParser st Entity
parseEntity pm =
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

parseTypedLiteral :: GA.PrefixMap -> CharParser st Literal
parseTypedLiteral pm =do
    char '"'
    s <- manyTill charOrEscaped (try $ char '"')
    string "^^"
    iri <- parseIRI
    return $ Literal s (Typed iri)

parseLanguageTag :: GA.PrefixMap -> CharParser st String
parseLanguageTag pm =do
    char '@'
    many1 (letter <|?> char '-')

parseUntypedLiteral :: GA.PrefixMap -> CharParser st Literal
parseUntypedLiteral pm =do
    char '"'
    s <- manyTill charOrEscaped (try $ char '"')
    languageTag <- optionMaybe (try parseLanguageTag)
    return $ Literal s (Untyped languageTag)

parseLiteral :: GA.PrefixMap -> CharParser st Literal
parseLiteral pm =skipsp (parseTypedLiteral <|?> parseUntypedLiteral) <?> "Literal"

-- ## Individuals

parseAnonymousIndividual :: GA.PrefixMap -> CharParser st AnonymousIndividual
parseAnonymousIndividual pm =iriCurie


parseIndividual :: GA.PrefixMap -> CharParser st Individual
parseIndividual pm =skipsp parseIRI <|?> skipsp parseAnonymousIndividual <?>
    "Individual"

-- # Annotations
parseAnnotationValue :: GA.PrefixMap -> CharParser st AnnotationValue
parseAnnotationValue pm =
     (parseLiteral >>= return . AnnValLit) <|?>
     (skipsp parseIRI >>= return . AnnValue) <|?>
     (skipsp parseAnonymousIndividual >>= return . AnnAnInd) <?>
     "AnnotationValue"

parseAnnotationSubject :: GA.PrefixMap -> CharParser st AnnotationSubject
parseAnnotationSubject pm =
    (AnnSubAnInd <$> skipsp parseAnonymousIndividual) <|?>
    (AnnSubIri <$> skipsp parseIRI)

parseAnnotations :: GA.PrefixMap -> CharParser st [Annotation]
parseAnnotations pm =manySkip parseAnnotation

parseAnnotation :: GA.PrefixMap -> CharParser st Annotation
parseAnnotation pm =(flip (<?>)) "Annotation" $
    parseEnclosedWithKeyword "Annotation" $ do
        an <- (manySkip (try parseAnnotation))
        skips
        property <- parseIRI
        skips
        v <- parseAnnotationValue
        return $ Annotation an property v

parseIriIfNotImportOrAxiomOrAnnotation :: GA.PrefixMap -> CharParser st (Maybe IRI)
parseIriIfNotImportOrAxiomOrAnnotation pm =
    (arbitraryLookaheadOption [
        forget parseDirectlyImportsDocument,
        forget parseAnnotation,
        forget parseAxiom
    ] >> never) <|>
    optionMaybe parseIRI


-- ## Data Range

parseDataJunction' :: GA.PrefixMap -> String -> JunctionType -> CharParser st DataRange
parseDataJunction' pm k t = parseEnclosedWithKeyword k $
    DataJunction t <$> manyNSkip 2 parseDataRange

parseDataJunction :: GA.PrefixMap -> CharParser st DataRange
parseDataJunction pm =
    parseDataJunction' "DataUnionOf" UnionOf <|?>
    parseDataJunction' "DataIntersectionOf" IntersectionOf

parseDataComplementOf :: GA.PrefixMap -> CharParser st DataRange
parseDataComplementOf pm =parseEnclosedWithKeyword "DataComplementOf" $
    DataComplementOf <$> parseDataRange

parseDataOneOf :: GA.PrefixMap -> CharParser st DataRange
parseDataOneOf pm =parseEnclosedWithKeyword "DataOneOf" $
    DataOneOf <$> many1Skip parseLiteral

parseDatatypeResComponent :: GA.PrefixMap -> CharParser st (ConstrainingFacet, RestrictionValue)
parseDatatypeResComponent pm =
    (,) <$>
    skipsp parseIRI <*>
    parseLiteral

parseDatatypeRestriction :: GA.PrefixMap -> CharParser st DataRange
parseDatatypeRestriction pm =parseEnclosedWithKeyword "DatatypeRestriction" $ do
    dataType <- parseIRI
    skips
    restrictions <- many1Skip parseDatatypeResComponent
    return $ DataType dataType restrictions

parseDataRange :: GA.PrefixMap -> CharParser st DataRange
parseDataRange pm =
    parseDataJunction <|?>
    parseDataComplementOf <|?>
    parseDataOneOf <|?>
    parseDatatypeRestriction <|?>
    (DataType <$> skipsp parseIRI <*> return []) <?>
    "DataRange"

{- # Axioms

## Declaration -}

parseDeclaration :: GA.PrefixMap -> CharParser st Axiom
parseDeclaration pm =parseEnclosedWithKeyword "Declaration" $ do
    annotations <- manySkip parseAnnotation
    skips
    entity <- parseEntity
    return $ Declaration annotations entity

-- ## ClassExpressions

parseObjectIntersectionOf :: GA.PrefixMap -> CharParser st ClassExpression
parseObjectIntersectionOf pm =parseEnclosedWithKeyword "ObjectIntersectionOf" $
    ObjectJunction IntersectionOf <$> manyNSkip 2 parseClassExpression

parseObjectUnionOf :: GA.PrefixMap -> CharParser st ClassExpression
parseObjectUnionOf pm =parseEnclosedWithKeyword "ObjectUnionOf" $
    ObjectJunction UnionOf <$> manyNSkip 2 parseClassExpression

parseObjectComplementOf :: GA.PrefixMap -> CharParser st ClassExpression
parseObjectComplementOf pm =parseEnclosedWithKeyword "ObjectComplementOf" $
    ObjectComplementOf <$> parseClassExpression

parseObjectOneOf :: GA.PrefixMap -> CharParser st ClassExpression
parseObjectOneOf pm =parseEnclosedWithKeyword "ObjectOneOf" $
    ObjectOneOf <$> many1Skip parseIndividual

parseObjectProperty :: GA.PrefixMap -> CharParser st ObjectPropertyExpression
parseObjectProperty pm =ObjectProp <$> skipsp parseIRI

parseInverseObjectProperty :: GA.PrefixMap -> CharParser st ObjectPropertyExpression
parseInverseObjectProperty pm =parseEnclosedWithKeyword "ObjectInverseOf" $
    ObjectInverseOf <$> parseObjectProperty

parseObjectPropertyExpression :: GA.PrefixMap -> CharParser st ObjectPropertyExpression
parseObjectPropertyExpression pm =
    parseInverseObjectProperty <|?>
    parseObjectProperty <?>
    "ObjectPropertyExpression"


parseObjectSomeValuesFrom :: GA.PrefixMap -> CharParser st ClassExpression
parseObjectSomeValuesFrom pm =parseEnclosedWithKeyword "ObjectSomeValuesFrom" $ do
    objectPropertyExpr <- parseObjectPropertyExpression
    skips
    classExpr <- parseClassExpression
    return $ ObjectValuesFrom SomeValuesFrom objectPropertyExpr classExpr

parseObjectAllValuesFrom :: GA.PrefixMap -> CharParser st ClassExpression
parseObjectAllValuesFrom pm =parseEnclosedWithKeyword "ObjectAllValuesFrom" $ do
    objectPropertyExpr <- parseObjectPropertyExpression
    skips
    classExpr <- parseClassExpression
    return $ ObjectValuesFrom AllValuesFrom objectPropertyExpr classExpr

parseObjectHasValue :: GA.PrefixMap -> CharParser st ClassExpression
parseObjectHasValue pm =parseEnclosedWithKeyword "ObjectHasValue" $ do
    objectPropertyExpr <- parseObjectPropertyExpression
    skips
    val <- parseIndividual
    return $ ObjectHasValue objectPropertyExpr val

parseObjectHasSelf :: GA.PrefixMap -> CharParser st ClassExpression
parseObjectHasSelf pm =parseEnclosedWithKeyword "ObjectHasSelf" $
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

parseObjectCardinality :: GA.PrefixMap -> CharParser st ClassExpression
parseObjectCardinality pm =ObjectCardinality <$> (
        cardinality "ObjectMinCardinality" MinCardinality <|?>
        cardinality "ObjectMaxCardinality" MaxCardinality <|?>
        cardinality "ObjectExactCardinality" ExactCardinality
    )
    where cardinality s t = (parseCardinality' t s a b)
          a = parseObjectPropertyExpression
          b = parseClassExpression

parseDataCardinality :: GA.PrefixMap -> CharParser st ClassExpression
parseDataCardinality pm =DataCardinality <$> (
        cardinality "DataMinCardinality" MinCardinality <|?>
        cardinality "DataMaxCardinality" MaxCardinality <|?>
        cardinality "DataExactCardinality" ExactCardinality
    )
    where cardinality s t = (parseCardinality' t s a b)
          a = parseIRI
          b = parseDataRange


parseDataSomeValuesFrom :: GA.PrefixMap -> CharParser st ClassExpression
parseDataSomeValuesFrom pm =parseEnclosedWithKeyword "DataSomeValuesFrom" $ do
    exprs <- many1 (followedBy (skipsp parseDataRange) (skipsp parseIRI))
    skips
    range <- parseDataRange
    return $ DataValuesFrom SomeValuesFrom exprs range

parseDataAllValuesFrom :: GA.PrefixMap -> CharParser st ClassExpression
parseDataAllValuesFrom pm =parseEnclosedWithKeyword "DataAllValuesFrom" $ do
    exprs <- many1 (followedBy parseDataRange (skipsp parseIRI))
    skips
    range <- parseDataRange
    return $ DataValuesFrom AllValuesFrom exprs range

parseDataHasValue :: GA.PrefixMap -> CharParser st ClassExpression
parseDataHasValue pm =parseEnclosedWithKeyword "DataHasValue" $
    DataHasValue <$> skipsp parseIRI <*> parseLiteral


parseClassExpression :: GA.PrefixMap -> CharParser st ClassExpression
parseClassExpression pm =
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

parseSubClassOf :: GA.PrefixMap -> CharParser st ClassAxiom
parseSubClassOf pm =parseEnclosedWithKeyword "SubClassOf" $ do
    annotations <- manySkip parseAnnotation
    skips
    subClassExpression <- parseClassExpression
    skips
    superClassExpression <- parseClassExpression
    return $ SubClassOf annotations subClassExpression superClassExpression

parseEquivalentClasses :: GA.PrefixMap -> CharParser st ClassAxiom
parseEquivalentClasses pm =parseEnclosedWithKeyword "EquivalentClasses" $
    EquivalentClasses <$> parseAnnotations <*> manyNSkip 2 parseClassExpression

parseDisjointClasses :: GA.PrefixMap -> CharParser st ClassAxiom
parseDisjointClasses pm =parseEnclosedWithKeyword "DisjointClasses" $
    DisjointClasses <$> parseAnnotations <*> manyNSkip 2 parseClassExpression

parseDisjointUnion :: GA.PrefixMap -> CharParser st ClassAxiom
parseDisjointUnion pm =parseEnclosedWithKeyword "DisjointUnion" $
    DisjointUnion <$>
    parseAnnotations <*>
    skipsp parseIRI <*>
    manyNSkip 2 parseClassExpression

parseClassAxiom :: GA.PrefixMap -> CharParser st Axiom
parseClassAxiom pm =ClassAxiom <$> (
        parseSubClassOf <|?>
        parseEquivalentClasses <|?>
        parseDisjointClasses <|?>
        parseDisjointUnion <?> "ClassAxiom"
    )

-- ## Object Property Axioms

parseEquivalentObjectProperties :: GA.PrefixMap -> CharParser st ObjectPropertyAxiom
parseEquivalentObjectProperties pm =
    parseEnclosedWithKeyword "EquivalentObjectProperties" $
    EquivalentObjectProperties <$>
    parseAnnotations <*>
    manyNSkip 2 parseObjectPropertyExpression

parseDisjointObjectProperties :: GA.PrefixMap -> CharParser st ObjectPropertyAxiom
parseDisjointObjectProperties pm =
    parseEnclosedWithKeyword "DisjointObjectProperties" $
    DisjointObjectProperties <$>
    parseAnnotations <*>
    manyNSkip 2 parseObjectPropertyExpression

parseObjectPropertyDomain :: GA.PrefixMap -> CharParser st ObjectPropertyAxiom
parseObjectPropertyDomain pm =
    parseEnclosedWithKeyword "ObjectPropertyDomain" $
    ObjectPropertyDomain <$>
    parseAnnotations <*>
    parseObjectPropertyExpression <*>
    parseClassExpression

parseObjectPropertyRange :: GA.PrefixMap -> CharParser st ObjectPropertyAxiom
parseObjectPropertyRange pm =
    parseEnclosedWithKeyword "ObjectPropertyRange" $
    ObjectPropertyRange <$>
    parseAnnotations <*>
    parseObjectPropertyExpression <*>
    parseClassExpression

parseInverseObjectProperties :: GA.PrefixMap -> CharParser st ObjectPropertyAxiom
parseInverseObjectProperties pm =
    parseEnclosedWithKeyword "InverseObjectProperties" $
    InverseObjectProperties <$>
    parseAnnotations <*>
    parseObjectPropertyExpression <*>
    parseObjectPropertyExpression


-- ### SubObjectPropertyOf
parseObjectPropertyExpressionChain :: GA.PrefixMap -> CharParser st PropertyExpressionChain
parseObjectPropertyExpressionChain pm =
    parseEnclosedWithKeyword "ObjectPropertyChain" $
    manyNSkip 2 parseObjectPropertyExpression

parseSubObjectPropertyExpression :: GA.PrefixMap -> CharParser st SubObjectPropertyExpression
parseSubObjectPropertyExpression pm =
    SubObjPropExpr_exprchain <$> parseObjectPropertyExpressionChain <|?>
    SubObjPropExpr_obj <$> parseObjectPropertyExpression <?>
    "SubObjectPropertyExpression"

parseSubObjectPropertyOf :: GA.PrefixMap -> CharParser st ObjectPropertyAxiom
parseSubObjectPropertyOf pm =parseEnclosedWithKeyword "SubObjectPropertyOf" $
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

parseObjectPropertyAxiom :: GA.PrefixMap -> CharParser st Axiom
parseObjectPropertyAxiom pm =ObjectPropertyAxiom <$> (
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

parseSubDataPropertyOf :: GA.PrefixMap -> CharParser st DataPropertyAxiom
parseSubDataPropertyOf pm =parseEnclosedWithKeyword "SubDataPropertyOf" $
    SubDataPropertyOf <$>
    parseAnnotations <*>
    skipsp parseIRI <*>
    skipsp parseIRI

parseEquivalentDataProperties :: GA.PrefixMap -> CharParser st DataPropertyAxiom
parseEquivalentDataProperties pm =
    parseEnclosedWithKeyword "EquivalentDataProperties" $
    EquivalentDataProperties <$>
    parseAnnotations <*>
    manyNSkip 2 parseIRI

parseDisjointDataProperties :: GA.PrefixMap -> CharParser st DataPropertyAxiom
parseDisjointDataProperties pm =
    parseEnclosedWithKeyword "DisjointDataProperties" $
    DisjointDataProperties <$>
    parseAnnotations <*>
    manyNSkip 2 parseIRI

parseDataPropertyDomain :: GA.PrefixMap -> CharParser st DataPropertyAxiom
parseDataPropertyDomain pm =
    parseEnclosedWithKeyword "DataPropertyDomain" $
    DataPropertyDomain <$>
    parseAnnotations <*>
    skipsp parseIRI <*>
    parseClassExpression

parseDataPropertyRange :: GA.PrefixMap -> CharParser st DataPropertyAxiom
parseDataPropertyRange pm =
    parseEnclosedWithKeyword "DataPropertyRange" $
    DataPropertyRange <$>
    parseAnnotations <*>
    skipsp parseIRI <*>
    parseDataRange

parseFunctionalDataProperty :: GA.PrefixMap -> CharParser st DataPropertyAxiom
parseFunctionalDataProperty pm =
    parseEnclosedWithKeyword "FunctionalDataProperty" $
    FunctionalDataProperty <$>
    parseAnnotations <*>
    skipsp parseIRI

parseDataPropertyAxiom :: GA.PrefixMap -> CharParser st Axiom
parseDataPropertyAxiom pm =DataPropertyAxiom <$> (
        parseSubDataPropertyOf <|?>
        parseEquivalentDataProperties <|?>
        parseDisjointDataProperties <|?>
        parseDataPropertyDomain <|?>
        parseDataPropertyRange <|?>
        parseFunctionalDataProperty <?>
        "DataPropertyAxiom"
    )

-- ## Data Type Definition
parseDataTypeDefinition :: GA.PrefixMap -> CharParser st Axiom
parseDataTypeDefinition pm =parseEnclosedWithKeyword "DatatypeDefinition" $
    DatatypeDefinition <$>
    parseAnnotations <*>
    skipsp parseIRI <*>
    parseDataRange

-- ## HasKey
parseHasKey :: GA.PrefixMap -> CharParser st Axiom
parseHasKey pm =parseEnclosedWithKeyword "HasKey" $ do
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
parseSameIndividual :: GA.PrefixMap -> CharParser st Assertion
parseSameIndividual pm =parseEnclosedWithKeyword "SameIndividual" $
    SameIndividual <$>
    parseAnnotations <*>
    manyNSkip 2 parseIndividual

parseDifferentIndividuals :: GA.PrefixMap -> CharParser st Assertion
parseDifferentIndividuals pm =parseEnclosedWithKeyword "DifferentIndividuals" $
    DifferentIndividuals <$>
    parseAnnotations <*>
    manyNSkip 2 parseIndividual

parseClassAssertion :: GA.PrefixMap -> CharParser st Assertion
parseClassAssertion pm =parseEnclosedWithKeyword "ClassAssertion" $
    ClassAssertion <$>
    parseAnnotations <*>
    parseClassExpression <*>
    parseIndividual

parseObjectPropertyAssertion :: GA.PrefixMap -> CharParser st Assertion
parseObjectPropertyAssertion pm =
    parseEnclosedWithKeyword "ObjectPropertyAssertion" $
    ObjectPropertyAssertion <$>
    parseAnnotations <*>
    parseObjectPropertyExpression <*>
    parseIndividual <*>
    parseIndividual

parseNegativeObjectPropertyAssertion :: GA.PrefixMap -> CharParser st Assertion
parseNegativeObjectPropertyAssertion pm =
    parseEnclosedWithKeyword "NegativeObjectPropertyAssertion" $
    NegativeObjectPropertyAssertion <$>
    parseAnnotations <*>
    parseObjectPropertyExpression <*>
    parseIndividual <*>
    parseIndividual

parseDataPropertyAssertion :: GA.PrefixMap -> CharParser st Assertion
parseDataPropertyAssertion pm =
    parseEnclosedWithKeyword "DataPropertyAssertion" $
    DataPropertyAssertion <$>
    parseAnnotations <*>
    skipsp parseIRI <*>
    parseIndividual <*>
    parseLiteral

parseNegativeDataPropertyAssertion :: GA.PrefixMap -> CharParser st Assertion
parseNegativeDataPropertyAssertion pm =
    parseEnclosedWithKeyword "NegativeDataPropertyAssertion" $
    NegativeDataPropertyAssertion <$>
    parseAnnotations <*>
    skipsp parseIRI <*>
    parseIndividual <*>
    parseLiteral

parseAssertion :: GA.PrefixMap -> CharParser st Axiom
parseAssertion pm =Assertion <$> (
        parseSameIndividual <|?>
        parseDifferentIndividuals <|?>
        parseClassAssertion <|?>
        parseObjectPropertyAssertion <|?>
        parseNegativeObjectPropertyAssertion <|?>
        parseDataPropertyAssertion <|?>
        parseNegativeDataPropertyAssertion
    )


parseAnnotationAssertion :: GA.PrefixMap -> CharParser st AnnotationAxiom
parseAnnotationAssertion pm =parseEnclosedWithKeyword "AnnotationAssertion" $
    AnnotationAssertion <$>
    parseAnnotations <*>
    skipsp parseIRI <*>
    parseAnnotationSubject <*>
    parseAnnotationValue

parseSubAnnotationPropertyOf :: GA.PrefixMap -> CharParser st AnnotationAxiom
parseSubAnnotationPropertyOf pm =
    parseEnclosedWithKeyword "SubAnnotationPropertyOf" $
    SubAnnotationPropertyOf <$>
    parseAnnotations <*>
    skipsp parseIRI <*>
    skipsp parseIRI

parseAnnotationPropertyDomain :: GA.PrefixMap -> CharParser st AnnotationAxiom
parseAnnotationPropertyDomain pm =
    parseEnclosedWithKeyword "AnnotationPropertyDomain" $
    AnnotationPropertyDomain <$>
    parseAnnotations <*>
    skipsp parseIRI <*>
    skipsp parseIRI

parseAnnotationPropertyRange :: GA.PrefixMap -> CharParser st AnnotationAxiom
parseAnnotationPropertyRange pm =
    parseEnclosedWithKeyword "AnnotationPropertyRange" $
    AnnotationPropertyRange <$>
    parseAnnotations <*>
    skipsp parseIRI <*>
    skipsp parseIRI

parseAnnotationAxiom :: GA.PrefixMap -> CharParser st Axiom
parseAnnotationAxiom pm =AnnotationAxiom <$> (
        parseAnnotationAssertion <|?>
        parseSubAnnotationPropertyOf <|?>
        parseAnnotationPropertyDomain <|?>
        parseAnnotationPropertyRange
    )

parseAxiom :: GA.PrefixMap -> CharParser st Axiom
parseAxiom pm =
    parseDeclaration <|?>
    parseClassAxiom <|?>
    parseObjectPropertyAxiom <|?>
    parseDataPropertyAxiom <|?>
    parseDataTypeDefinition <|?>
    parseHasKey <|?>
    parseAssertion <|?>
    parseAnnotationAxiom <?>
    "Axiom"


parseOntology :: GA.PrefixMap -> CharParser st Ontology
parseOntology pm = parseEnclosedWithKeyword "Ontology" $ do
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

prefixFromMap :: GA.PrefixMap -> [PrefixDeclaration]
prefixFromMap = map (uncurry PrefixDeclaration) . toList

prefixToMap :: [PrefixDeclaration] -> GA.PrefixMap
prefixToMap = fromList . map (\(PrefixDeclaration name iri) -> (name, iri))


-- | Parses an OntologyDocument from Owl2 Functional Syntax
parseOntologyDocument :: GA.PrefixMap -> CharParser st OntologyDocument
parseOntologyDocument gapm = do
    prefix <- manySkip parsePrefixDeclaration
    skips
    let pm = union gapm (prefixToMap prefix)
    onto <- parseOntology pm
    return $ Ontology (prefixFromMap pm) onto

