{-# LANGUAGE TupleSections #-}

module OWL2.ParseAS where

import Prelude hiding (lookup)

import OWL2.AS

import Common.AnnoParser (newlineOrEof)
import Common.IRI hiding (parseIRI)
import Common.Parsec
import Common.Lexer (getNumber, value)
import qualified Common.GlobalAnnotations as GA (PrefixMap)

import Text.ParserCombinators.Parsec

import Data.Char
import Data.Map (union, toList, fromList,lookup)
import Data.Maybe


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

-- | @expandIRI pm iri@ returns the expanded @iri@ with a declaration from @pm@.
-- | If no declaration is found, return @iri@ unchanged.
expandIRI :: GA.PrefixMap -> IRI -> IRI
expandIRI pm iri
    | isAbbrev iri = fromMaybe iri $ do
        def <- lookup (prefixName iri) pm
        expanded <- mergeCurie iri def
        return $ expanded
            { iFragment = iFragment iri
            , prefixName = prefixName iri }
    | otherwise = iri

-- | Parses an abbreviated or full iri
parseIRI :: GA.PrefixMap -> CharParser st IRI
parseIRI pm = expandIRI pm <$> (fullIri <|?> compoundIriCurie) <?> "IRI"


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

parseDirectlyImportsDocument :: GA.PrefixMap -> CharParser st IRI
parseDirectlyImportsDocument pm = parseEnclosedWithKeyword "Import" (parseIRI pm) <?>
    "Import"

-- # Entities, Literals, and Individuals

-- ## Entities
parseEntity' :: GA.PrefixMap -> EntityType -> String -> CharParser st Entity
parseEntity' pm t k = parseEnclosedWithKeyword k $ do
    iri <- skipsp (parseIRI pm)
    return $ mkEntity t iri

parseEntity :: GA.PrefixMap -> CharParser st Entity
parseEntity pm =
    parseEntity' pm Class "Class" <|?>
    parseEntity' pm Datatype "Datatype" <|?>
    parseEntity' pm ObjectProperty "ObjectProperty" <|?>
    parseEntity' pm DataProperty "DataProperty" <|?>
    parseEntity' pm AnnotationProperty "AnnotationProperty" <|?>
    parseEntity' pm NamedIndividual "NamedIndividual" <?>
    "Entity"

-- ## Literals


charOrEscaped :: CharParser st Char
charOrEscaped = try (string "\\\"" >> return '"')
            <|> try (string "\\\\" >> return '\\') <|> anyChar

parseTypedLiteral :: GA.PrefixMap -> CharParser st Literal
parseTypedLiteral pm = do
    char '"'
    s <- manyTill charOrEscaped (try $ char '"')
    string "^^"
    iri <- (parseIRI pm)
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

parseLiteral :: GA.PrefixMap -> CharParser st Literal
parseLiteral pm = skipsp (parseTypedLiteral pm) <|?> parseUntypedLiteral <?> "Literal"

-- ## Individuals

parseAnonymousIndividual :: GA.PrefixMap -> CharParser st AnonymousIndividual
parseAnonymousIndividual pm = iriCurie


parseIndividual :: GA.PrefixMap -> CharParser st Individual
parseIndividual pm = skipsp (parseIRI pm) <|?> skipsp (parseAnonymousIndividual pm) <?>
    "Individual"

-- # Annotations
parseAnnotationValue :: GA.PrefixMap -> CharParser st AnnotationValue
parseAnnotationValue pm =
     ((parseLiteral pm) >>= return . AnnValLit) <|?>
     (skipsp (parseIRI pm) >>= return . AnnValue) <|?>
     (skipsp (parseAnonymousIndividual pm) >>= return . AnnAnInd) <?>
     "AnnotationValue"

parseAnnotationSubject :: GA.PrefixMap -> CharParser st AnnotationSubject
parseAnnotationSubject pm =
    (AnnSubAnInd <$> skipsp (parseAnonymousIndividual pm)) <|?>
    (AnnSubIri <$> skipsp (parseIRI pm))

parseAnnotations :: GA.PrefixMap -> CharParser st [Annotation]
parseAnnotations pm = manySkip (parseAnnotation pm)

parseAnnotation :: GA.PrefixMap -> CharParser st Annotation
parseAnnotation pm = (flip (<?>)) "Annotation" $
    parseEnclosedWithKeyword "Annotation" $ do
        an <- (manySkip (try (parseAnnotation pm)))
        skips
        property <- (parseIRI pm)
        skips
        v <- (parseAnnotationValue pm)
        return $ Annotation an property v

parseIriIfNotImportOrAxiomOrAnnotation :: GA.PrefixMap -> CharParser st (Maybe IRI)
parseIriIfNotImportOrAxiomOrAnnotation pm =
    (arbitraryLookaheadOption [
        forget (parseDirectlyImportsDocument pm),
        forget (parseAnnotation pm),
        forget (parseAxiom pm)
    ] >> never) <|>
    optionMaybe (parseIRI pm)


-- ## Data Range

parseDataJunction' :: GA.PrefixMap -> String -> JunctionType -> CharParser st DataRange
parseDataJunction' pm k t = parseEnclosedWithKeyword k $
    DataJunction t <$> manyNSkip 2 (parseDataRange pm)

parseDataJunction :: GA.PrefixMap -> CharParser st DataRange
parseDataJunction pm =
    parseDataJunction' pm "DataUnionOf" UnionOf <|?>
    parseDataJunction' pm "DataIntersectionOf" IntersectionOf

parseDataComplementOf :: GA.PrefixMap -> CharParser st DataRange
parseDataComplementOf pm = parseEnclosedWithKeyword "DataComplementOf" $
    DataComplementOf <$> parseDataRange pm

parseDataOneOf :: GA.PrefixMap -> CharParser st DataRange
parseDataOneOf pm = parseEnclosedWithKeyword "DataOneOf" $
    DataOneOf <$> many1Skip (parseLiteral pm)

parseDatatypeResComponent :: GA.PrefixMap -> CharParser st (ConstrainingFacet, RestrictionValue)
parseDatatypeResComponent pm =
    (,) <$>
    skipsp (parseIRI pm) <*>
    (parseLiteral pm)

parseDatatypeRestriction :: GA.PrefixMap -> CharParser st DataRange
parseDatatypeRestriction pm = parseEnclosedWithKeyword "DatatypeRestriction" $ do
    dataType <- (parseIRI pm)
    skips
    restrictions <- many1Skip (parseDatatypeResComponent pm)
    return $ DataType dataType restrictions

parseDataRange :: GA.PrefixMap -> CharParser st DataRange
parseDataRange pm =
    (parseDataJunction pm) <|?>
    (parseDataComplementOf pm) <|?>
    (parseDataOneOf pm) <|?>
    (parseDatatypeRestriction pm) <|?>
    (DataType <$> skipsp (parseIRI pm) <*> return []) <?>
    "DataRange"

{- # Axioms

## Declaration -}

parseDeclaration :: GA.PrefixMap -> CharParser st Axiom
parseDeclaration pm = parseEnclosedWithKeyword "Declaration" $ do
    annotations <- manySkip (parseAnnotation pm)
    skips
    entity <- (parseEntity pm)
    return $ Declaration annotations entity

-- ## ClassExpressions

parseObjectIntersectionOf :: GA.PrefixMap -> CharParser st ClassExpression
parseObjectIntersectionOf pm = parseEnclosedWithKeyword "ObjectIntersectionOf" $
    ObjectJunction IntersectionOf <$> manyNSkip 2 (parseClassExpression pm)

parseObjectUnionOf :: GA.PrefixMap -> CharParser st ClassExpression
parseObjectUnionOf pm = parseEnclosedWithKeyword "ObjectUnionOf" $
    ObjectJunction UnionOf <$> manyNSkip 2 (parseClassExpression pm)

parseObjectComplementOf :: GA.PrefixMap -> CharParser st ClassExpression
parseObjectComplementOf pm = parseEnclosedWithKeyword "ObjectComplementOf" $
    ObjectComplementOf <$> (parseClassExpression pm)

parseObjectOneOf :: GA.PrefixMap -> CharParser st ClassExpression
parseObjectOneOf pm = parseEnclosedWithKeyword "ObjectOneOf" $
    ObjectOneOf <$> many1Skip (parseIndividual pm)

parseObjectProperty :: GA.PrefixMap -> CharParser st ObjectPropertyExpression
parseObjectProperty pm = ObjectProp <$> skipsp (parseIRI pm)

parseInverseObjectProperty :: GA.PrefixMap -> CharParser st ObjectPropertyExpression
parseInverseObjectProperty pm = parseEnclosedWithKeyword "ObjectInverseOf" $
    ObjectInverseOf <$> (parseObjectProperty pm)

parseObjectPropertyExpression :: GA.PrefixMap -> CharParser st ObjectPropertyExpression
parseObjectPropertyExpression pm =
    (parseInverseObjectProperty pm) <|?>
    (parseObjectProperty pm) <?>
    "ObjectPropertyExpression"


parseObjectSomeValuesFrom :: GA.PrefixMap -> CharParser st ClassExpression
parseObjectSomeValuesFrom pm = parseEnclosedWithKeyword "ObjectSomeValuesFrom" $ do
    objectPropertyExpr <- (parseObjectPropertyExpression pm)
    skips
    classExpr <- (parseClassExpression pm)
    return $ ObjectValuesFrom SomeValuesFrom objectPropertyExpr classExpr

parseObjectAllValuesFrom :: GA.PrefixMap -> CharParser st ClassExpression
parseObjectAllValuesFrom pm = parseEnclosedWithKeyword "ObjectAllValuesFrom" $ do
    objectPropertyExpr <- (parseObjectPropertyExpression pm)
    skips
    classExpr <- (parseClassExpression pm)
    return $ ObjectValuesFrom AllValuesFrom objectPropertyExpr classExpr

parseObjectHasValue :: GA.PrefixMap -> CharParser st ClassExpression
parseObjectHasValue pm = parseEnclosedWithKeyword "ObjectHasValue" $ do
    objectPropertyExpr <- (parseObjectPropertyExpression pm)
    skips
    val <- (parseIndividual pm)
    return $ ObjectHasValue objectPropertyExpr val

parseObjectHasSelf :: GA.PrefixMap -> CharParser st ClassExpression
parseObjectHasSelf pm = parseEnclosedWithKeyword "ObjectHasSelf" $
    ObjectHasSelf <$> (parseObjectPropertyExpression pm)

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
parseObjectCardinality pm = ObjectCardinality <$> (
        cardinality "ObjectMinCardinality" MinCardinality <|?>
        cardinality "ObjectMaxCardinality" MaxCardinality <|?>
        cardinality "ObjectExactCardinality" ExactCardinality
    )
    where cardinality s t = parseCardinality' t s a b
          a = (parseObjectPropertyExpression pm)
          b = (parseClassExpression pm)

parseDataCardinality :: GA.PrefixMap -> CharParser st ClassExpression
parseDataCardinality pm = DataCardinality <$> (
        cardinality "DataMinCardinality" MinCardinality <|?>
        cardinality "DataMaxCardinality" MaxCardinality <|?>
        cardinality "DataExactCardinality" ExactCardinality
    )
    where cardinality s t = parseCardinality' t s a b
          a = (parseIRI pm)
          b = (parseDataRange pm)


parseDataSomeValuesFrom :: GA.PrefixMap -> CharParser st ClassExpression
parseDataSomeValuesFrom pm = parseEnclosedWithKeyword "DataSomeValuesFrom" $ do
    exprs <- many1 (followedBy (skipsp (parseDataRange pm)) (skipsp (parseIRI pm)))
    skips
    range <- (parseDataRange pm)
    return $ DataValuesFrom SomeValuesFrom exprs range

parseDataAllValuesFrom :: GA.PrefixMap -> CharParser st ClassExpression
parseDataAllValuesFrom pm = parseEnclosedWithKeyword "DataAllValuesFrom" $ do
    exprs <- many1 (followedBy (parseDataRange pm) (skipsp (parseIRI pm)))
    skips
    range <- (parseDataRange pm)
    return $ DataValuesFrom AllValuesFrom exprs range

parseDataHasValue :: GA.PrefixMap -> CharParser st ClassExpression
parseDataHasValue pm = parseEnclosedWithKeyword "DataHasValue" $
    DataHasValue <$> skipsp (parseIRI pm) <*> (parseLiteral pm)


parseClassExpression :: GA.PrefixMap -> CharParser st ClassExpression
parseClassExpression pm =
    (parseObjectIntersectionOf pm) <|?>
    (parseObjectUnionOf pm) <|?>
    (parseObjectComplementOf pm) <|?>
    (parseObjectOneOf pm) <|?>
    (parseObjectCardinality pm) <|?>
    (parseObjectSomeValuesFrom pm) <|?>
    (parseObjectAllValuesFrom pm) <|?>
    (parseObjectHasValue pm) <|?>
    (parseObjectHasSelf pm) <|?>
    (parseDataSomeValuesFrom pm) <|?>
    (parseDataAllValuesFrom pm) <|?>
    (parseDataHasValue pm) <|?>
    (parseDataCardinality pm) <|?>
    (Expression <$> skipsp (parseIRI pm)) <?>
    "ClassExpression"

-- ## Class Axioms

parseSubClassOf :: GA.PrefixMap -> CharParser st ClassAxiom
parseSubClassOf pm = parseEnclosedWithKeyword "SubClassOf" $ do
    annotations <- manySkip (parseAnnotation pm)
    skips
    subClassExpression <- (parseClassExpression pm)
    skips
    superClassExpression <- (parseClassExpression pm)
    return $ SubClassOf annotations subClassExpression superClassExpression

parseEquivalentClasses :: GA.PrefixMap -> CharParser st ClassAxiom
parseEquivalentClasses pm = parseEnclosedWithKeyword "EquivalentClasses" $
    EquivalentClasses <$> (parseAnnotations pm) <*> manyNSkip 2 (parseClassExpression pm)

parseDisjointClasses :: GA.PrefixMap -> CharParser st ClassAxiom
parseDisjointClasses pm = parseEnclosedWithKeyword "DisjointClasses" $
    DisjointClasses <$> (parseAnnotations pm) <*> manyNSkip 2 (parseClassExpression pm)

parseDisjointUnion :: GA.PrefixMap -> CharParser st ClassAxiom
parseDisjointUnion pm = parseEnclosedWithKeyword "DisjointUnion" $
    DisjointUnion <$>
    (parseAnnotations pm) <*>
    skipsp (parseIRI pm) <*>
    manyNSkip 2 (parseClassExpression pm)

parseClassAxiom :: GA.PrefixMap -> CharParser st Axiom
parseClassAxiom pm = ClassAxiom <$> (
        (parseSubClassOf pm) <|?>
        (parseEquivalentClasses pm) <|?>
        (parseDisjointClasses pm) <|?>
        (parseDisjointUnion pm) <?> "ClassAxiom"
    )

-- ## Object Property Axioms

parseEquivalentObjectProperties :: GA.PrefixMap -> CharParser st ObjectPropertyAxiom
parseEquivalentObjectProperties pm =
    parseEnclosedWithKeyword "EquivalentObjectProperties" $
    EquivalentObjectProperties <$>
    (parseAnnotations pm) <*>
    manyNSkip 2 (parseObjectPropertyExpression pm)

parseDisjointObjectProperties :: GA.PrefixMap -> CharParser st ObjectPropertyAxiom
parseDisjointObjectProperties pm =
    parseEnclosedWithKeyword "DisjointObjectProperties" $
    DisjointObjectProperties <$>
    (parseAnnotations pm) <*>
    manyNSkip 2 (parseObjectPropertyExpression pm)

parseObjectPropertyDomain :: GA.PrefixMap -> CharParser st ObjectPropertyAxiom
parseObjectPropertyDomain pm =
    parseEnclosedWithKeyword "ObjectPropertyDomain" $
    ObjectPropertyDomain <$>
    (parseAnnotations pm) <*>
    (parseObjectPropertyExpression pm) <*>
    (parseClassExpression pm)

parseObjectPropertyRange :: GA.PrefixMap -> CharParser st ObjectPropertyAxiom
parseObjectPropertyRange pm =
    parseEnclosedWithKeyword "ObjectPropertyRange" $
    ObjectPropertyRange <$>
    (parseAnnotations pm) <*>
    (parseObjectPropertyExpression pm) <*>
    (parseClassExpression pm)

parseInverseObjectProperties :: GA.PrefixMap -> CharParser st ObjectPropertyAxiom
parseInverseObjectProperties pm =
    parseEnclosedWithKeyword "InverseObjectProperties" $
    InverseObjectProperties <$>
    (parseAnnotations pm) <*>
    (parseObjectPropertyExpression pm) <*>
    (parseObjectPropertyExpression pm)


-- ### SubObjectPropertyOf
parseObjectPropertyExpressionChain :: GA.PrefixMap -> CharParser st PropertyExpressionChain
parseObjectPropertyExpressionChain pm =
    parseEnclosedWithKeyword "ObjectPropertyChain" $
    manyNSkip 2 (parseObjectPropertyExpression pm)

parseSubObjectPropertyExpression :: GA.PrefixMap -> CharParser st SubObjectPropertyExpression
parseSubObjectPropertyExpression pm =
    SubObjPropExpr_exprchain <$> (parseObjectPropertyExpressionChain pm) <|?>
    SubObjPropExpr_obj <$> (parseObjectPropertyExpression pm) <?>
    "SubObjectPropertyExpression"

parseSubObjectPropertyOf :: GA.PrefixMap -> CharParser st ObjectPropertyAxiom
parseSubObjectPropertyOf pm = parseEnclosedWithKeyword "SubObjectPropertyOf" $
    SubObjectPropertyOf <$>
    (parseAnnotations pm) <*>
    (parseSubObjectPropertyExpression pm) <*>
    (parseObjectPropertyExpression pm)


-- | Helper function for *C*ommon*O*bject*P*roperty*A*xioms
parseCOPA :: GA.PrefixMap -> (
        AxiomAnnotations -> ObjectPropertyExpression -> ObjectPropertyAxiom
    ) -> String -> CharParser st ObjectPropertyAxiom
parseCOPA pm c s = parseEnclosedWithKeyword s $
    c <$>
    (parseAnnotations pm) <*>
    (parseObjectPropertyExpression pm)

parseObjectPropertyAxiom :: GA.PrefixMap -> CharParser st Axiom
parseObjectPropertyAxiom pm = ObjectPropertyAxiom <$> (
        (parseSubObjectPropertyOf pm) <|?>
        (parseEquivalentObjectProperties pm) <|?>
        (parseDisjointObjectProperties pm) <|?>
        (parseObjectPropertyDomain pm) <|?>
        (parseObjectPropertyRange pm) <|?>
        (parseInverseObjectProperties pm) <|?>
        parseCOPA pm FunctionalObjectProperty "FunctionalObjectProperty" <|?>
        parseCOPA pm InverseFunctionalObjectProperty
            "InverseFunctionalObjectProperty" <|?>
        parseCOPA pm ReflexiveObjectProperty "ReflexiveObjectProperty" <|?>
        parseCOPA pm IrreflexiveObjectProperty "IrreflexiveObjectProperty" <|?>
        parseCOPA pm SymmetricObjectProperty "SymmetricObjectProperty" <|?>
        parseCOPA pm AsymmetricObjectProperty "AsymmetricObjectProperty" <|?>
        parseCOPA pm TransitiveObjectProperty "TransitiveObjectProperty" <?>
        "ObjectPropertyAxiom"
    )

-- ## DataPropertyAxioms

parseSubDataPropertyOf :: GA.PrefixMap -> CharParser st DataPropertyAxiom
parseSubDataPropertyOf pm = parseEnclosedWithKeyword "SubDataPropertyOf" $
    SubDataPropertyOf <$>
    parseAnnotations pm <*>
    skipsp (parseIRI pm) <*>
    skipsp (parseIRI pm)

parseEquivalentDataProperties :: GA.PrefixMap -> CharParser st DataPropertyAxiom
parseEquivalentDataProperties pm =
    parseEnclosedWithKeyword "EquivalentDataProperties" $
    EquivalentDataProperties <$>
    (parseAnnotations pm) <*>
    manyNSkip 2 (parseIRI pm)

parseDisjointDataProperties :: GA.PrefixMap -> CharParser st DataPropertyAxiom
parseDisjointDataProperties pm =
    parseEnclosedWithKeyword "DisjointDataProperties" $
    DisjointDataProperties <$>
    parseAnnotations pm <*>
    manyNSkip 2 (parseIRI pm)

parseDataPropertyDomain :: GA.PrefixMap -> CharParser st DataPropertyAxiom
parseDataPropertyDomain pm =
    parseEnclosedWithKeyword "DataPropertyDomain" $
    DataPropertyDomain <$>
    parseAnnotations pm <*>
    skipsp (parseIRI pm) <*>
    parseClassExpression pm

parseDataPropertyRange :: GA.PrefixMap -> CharParser st DataPropertyAxiom
parseDataPropertyRange pm =
    parseEnclosedWithKeyword "DataPropertyRange" $
    DataPropertyRange <$>
    parseAnnotations pm <*>
    skipsp (parseIRI pm) <*>
    parseDataRange pm

parseFunctionalDataProperty :: GA.PrefixMap -> CharParser st DataPropertyAxiom
parseFunctionalDataProperty pm =
    parseEnclosedWithKeyword "FunctionalDataProperty" $
    FunctionalDataProperty <$>
    parseAnnotations pm <*>
    skipsp (parseIRI pm)

parseDataPropertyAxiom :: GA.PrefixMap -> CharParser st Axiom
parseDataPropertyAxiom pm = DataPropertyAxiom <$> (
        parseSubDataPropertyOf pm <|?>
        parseEquivalentDataProperties pm <|?>
        parseDisjointDataProperties pm <|?>
        parseDataPropertyDomain pm <|?>
        parseDataPropertyRange pm <|?>
        parseFunctionalDataProperty pm <?>
        "DataPropertyAxiom"
    )

-- ## Data Type Definition
parseDataTypeDefinition :: GA.PrefixMap -> CharParser st Axiom
parseDataTypeDefinition pm = parseEnclosedWithKeyword "DatatypeDefinition" $
    DatatypeDefinition <$>
    parseAnnotations pm <*>
    skipsp (parseIRI pm) <*>
    parseDataRange pm

-- ## HasKey
parseHasKey :: GA.PrefixMap -> CharParser st Axiom
parseHasKey pm = parseEnclosedWithKeyword "HasKey" $ do
    annotations <- (parseAnnotations pm)
    skips
    classExpr <- (parseClassExpression pm)
    skips
    char '('
    skips
    objectPropertyExprs <- manySkip (parseObjectPropertyExpression pm)
    skips
    char ')'
    skips
    char '('
    skips
    dataPropertyExprs <- manySkip (parseIRI pm)
    skips
    char ')'
    return $ HasKey annotations classExpr objectPropertyExprs dataPropertyExprs

-- ## Assertion
parseSameIndividual :: GA.PrefixMap -> CharParser st Assertion
parseSameIndividual pm = parseEnclosedWithKeyword "SameIndividual" $
    SameIndividual <$>
    (parseAnnotations pm) <*>
    manyNSkip 2 (parseIndividual pm)

parseDifferentIndividuals :: GA.PrefixMap -> CharParser st Assertion
parseDifferentIndividuals pm = parseEnclosedWithKeyword "DifferentIndividuals" $
    DifferentIndividuals <$>
    (parseAnnotations pm) <*>
    manyNSkip 2 (parseIndividual pm)

parseClassAssertion :: GA.PrefixMap -> CharParser st Assertion
parseClassAssertion pm = parseEnclosedWithKeyword "ClassAssertion" $
    ClassAssertion <$>
    (parseAnnotations pm) <*>
    (parseClassExpression pm) <*>
    (parseIndividual pm)

parseObjectPropertyAssertion :: GA.PrefixMap -> CharParser st Assertion
parseObjectPropertyAssertion pm =
    parseEnclosedWithKeyword "ObjectPropertyAssertion" $
    ObjectPropertyAssertion <$>
    (parseAnnotations pm) <*>
    (parseObjectPropertyExpression pm) <*>
    (parseIndividual pm) <*>
    (parseIndividual pm)

parseNegativeObjectPropertyAssertion :: GA.PrefixMap -> CharParser st Assertion
parseNegativeObjectPropertyAssertion pm =
    parseEnclosedWithKeyword "NegativeObjectPropertyAssertion" $
    NegativeObjectPropertyAssertion <$>
    (parseAnnotations pm) <*>
    (parseObjectPropertyExpression pm) <*>
    (parseIndividual pm) <*>
    (parseIndividual pm)

parseDataPropertyAssertion :: GA.PrefixMap -> CharParser st Assertion
parseDataPropertyAssertion pm =
    parseEnclosedWithKeyword "DataPropertyAssertion" $
    DataPropertyAssertion <$>
    (parseAnnotations pm) <*>
    skipsp (parseIRI pm) <*>
    (parseIndividual pm) <*>
    (parseLiteral pm)

parseNegativeDataPropertyAssertion :: GA.PrefixMap -> CharParser st Assertion
parseNegativeDataPropertyAssertion pm =
    parseEnclosedWithKeyword "NegativeDataPropertyAssertion" $
    NegativeDataPropertyAssertion <$>
    (parseAnnotations pm) <*>
    skipsp (parseIRI pm) <*>
    (parseIndividual pm) <*>
    (parseLiteral pm)

parseAssertion :: GA.PrefixMap -> CharParser st Axiom
parseAssertion pm = Assertion <$> (
        (parseSameIndividual pm) <|?>
        (parseDifferentIndividuals pm) <|?>
        (parseClassAssertion pm) <|?>
        (parseObjectPropertyAssertion pm) <|?>
        (parseNegativeObjectPropertyAssertion pm) <|?>
        (parseDataPropertyAssertion pm) <|?>
        (parseNegativeDataPropertyAssertion pm)
    )


parseAnnotationAssertion :: GA.PrefixMap -> CharParser st AnnotationAxiom
parseAnnotationAssertion pm = parseEnclosedWithKeyword "AnnotationAssertion" $
    AnnotationAssertion <$>
    (parseAnnotations pm) <*>
    skipsp (parseIRI pm) <*>
    (parseAnnotationSubject pm) <*>
    (parseAnnotationValue pm)

parseSubAnnotationPropertyOf :: GA.PrefixMap -> CharParser st AnnotationAxiom
parseSubAnnotationPropertyOf pm =
    parseEnclosedWithKeyword "SubAnnotationPropertyOf" $
    SubAnnotationPropertyOf <$>
    (parseAnnotations pm) <*>
    skipsp (parseIRI pm) <*>
    skipsp (parseIRI pm)

parseAnnotationPropertyDomain :: GA.PrefixMap -> CharParser st AnnotationAxiom
parseAnnotationPropertyDomain pm =
    parseEnclosedWithKeyword "AnnotationPropertyDomain" $
    AnnotationPropertyDomain <$>
    (parseAnnotations pm) <*>
    skipsp (parseIRI pm) <*>
    skipsp (parseIRI pm)

parseAnnotationPropertyRange :: GA.PrefixMap -> CharParser st AnnotationAxiom
parseAnnotationPropertyRange pm =
    parseEnclosedWithKeyword "AnnotationPropertyRange" $
    AnnotationPropertyRange <$>
    (parseAnnotations pm) <*>
    skipsp (parseIRI pm) <*>
    skipsp (parseIRI pm)

parseAnnotationAxiom :: GA.PrefixMap -> CharParser st Axiom
parseAnnotationAxiom pm = AnnotationAxiom <$> (
        (parseAnnotationAssertion pm) <|?>
        (parseSubAnnotationPropertyOf pm) <|?>
        (parseAnnotationPropertyDomain pm) <|?>
        (parseAnnotationPropertyRange pm)
    )

parseAxiom :: GA.PrefixMap -> CharParser st Axiom
parseAxiom pm =
    (parseDeclaration pm) <|?>
    (parseClassAxiom pm) <|?>
    (parseObjectPropertyAxiom pm) <|?>
    (parseDataPropertyAxiom pm) <|?>
    (parseDataTypeDefinition pm) <|?>
    (parseHasKey pm) <|?>
    (parseAssertion pm) <|?>
    (parseAnnotationAxiom pm) <?>
    "Axiom"


parseOntology :: GA.PrefixMap -> CharParser st Ontology
parseOntology pm = parseEnclosedWithKeyword "Ontology" $ do
    ontologyIri <- (parseIriIfNotImportOrAxiomOrAnnotation pm)
    skips
    versionIri <- (parseIriIfNotImportOrAxiomOrAnnotation pm)
    skips
    imports <- manySkip (parseDirectlyImportsDocument pm)
    skips
    annotations <- manySkip (parseAnnotation pm)
    skips
    axioms <- manySkip (parseAxiom pm)
    return $ Ontology ontologyIri versionIri (imports) annotations axioms

prefixFromMap :: GA.PrefixMap -> [PrefixDeclaration]
prefixFromMap = map (uncurry PrefixDeclaration) . toList

prefixToMap :: [PrefixDeclaration] -> GA.PrefixMap
prefixToMap = fromList . map (\ (PrefixDeclaration name iri) -> (name, iri))


-- | Parses an OntologyDocument from Owl2 Functional Syntax
parseOntologyDocument :: GA.PrefixMap -> CharParser st OntologyDocument
parseOntologyDocument gapm = do
    prefixes <- manySkip parsePrefixDeclaration
    skips
    let pm = union gapm (prefixToMap prefixes)
    onto <- parseOntology pm
    return $ OntologyDocument (prefixFromMap pm) onto