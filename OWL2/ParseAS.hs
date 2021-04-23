{-# LANGUAGE TupleSections #-}

module OWL2.ParserAS where

-- **TESTING PURPOSES ONLY**
import System.Directory
import Data.List

import OWL2.AS

import Common.AnnoParser (newlineOrEof)
import Common.IRI
import Common.Parsec
import Common.Lexer (getNumber, value)

import Text.ParserCombinators.Parsec

import Data.Char

(<|?>) :: (GenParser t st a ) -> (GenParser t st a) -> GenParser t st a
p <|?> q = try p <|> try q
infixr 1 <|?>

manySkip :: CharParser st a -> CharParser st [a]
manySkip p = many (p << skips)

many1Skip :: CharParser st a -> CharParser st [a]
many1Skip p = many1 (p << skips)

manyNSkip :: Int -> CharParser st a -> CharParser st [a]
manyNSkip n p =
    foldr (\ _ r -> (p << skips) <:> r) (return []) [1 .. n] <++>
    many (p << skips)

-- | parses a comment
comment :: CharParser st String
comment = try $ do
    char '#'
    manyTill anyChar newlineOrEof


-- | Skips whitespaces comments and nested comments
skips :: CharParser st ()
skips = (skipMany
        (forget space <|> forget comment <?> ""))


-- | plain string parser with skip
keyword :: String -> CharParser st ()
keyword s = do
    skips
    try (string s >> notFollowedBy alphaNum)

fullIri :: CharParser st IRI
fullIri = angles iriParser

ncNameStart :: Char -> Bool
ncNameStart c = isAlpha c || c == '_'

-- | rfc3987 plus '+' from scheme (scheme does not allow the dots)
ncNameChar :: Char -> Bool
ncNameChar c = isAlphaNum c || elem c ".+-_\183"

prefix :: CharParser st String
prefix = option "" (satisfy ncNameStart <:> many (satisfy ncNameChar))
    <++> string ":"

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
parseDirectlyImportsDocument = parseEnclosedWithKeyword "Import" iriCurie

parseAnonymousIndividual :: CharParser st AnonymousIndividual
parseAnonymousIndividual = many alphaNum

parseIndividual :: CharParser st Individual
parseIndividual =
    NamedIndividual_ <$> iriCurie <|?>
    AnonymousIndividual <$> parseAnonymousIndividual


parseTypedLiteral :: CharParser st Literal
parseTypedLiteral = do
    s <- stringLit
    string "^^"
    iri <- iriCurie
    return $ Literal s (Typed iri)

charOrEscaped :: CharParser st Char
charOrEscaped = try (string "\\\"" >> return '"')
            <|> try (string "\\\\" >> return '\\') <|> anyChar

parseUntypedLiteral :: CharParser st Literal
parseUntypedLiteral = do
    char '"'
    s <- manyTill charOrEscaped (try $ char '"')
    return $ Literal s (Untyped Nothing)

parseLiteral :: CharParser st Literal
parseLiteral = parseTypedLiteral <|?> parseUntypedLiteral

parseAnnotationValue :: CharParser st AnnotationValue
parseAnnotationValue =
     (parseLiteral >>= return . AnnValLit) <|?>
     (iriCurie >>= return . AnnValue) <|?>
     (parseAnonymousIndividual >>= return . AnnAnInd)

parseAnnotations :: CharParser st [Annotation]
parseAnnotations = manySkip parseAnnotation

parseAnnotation :: CharParser st Annotation
parseAnnotation = parseEnclosedWithKeyword "Annotation" $ do
    an <- (many (try parseAnnotation) << skips)
    skips
    property <- iriCurie
    skips
    v <- parseAnnotationValue
    return $ Annotation an property v

arbitraryLookaheadOption :: [CharParser st a] -> CharParser st a
arbitraryLookaheadOption p = lookAhead $ choice (try <$> p)

never :: CharParser st (Maybe a)
never = return Nothing

parseIriIfNotImportOrAxiom :: CharParser st (Maybe IRI)
parseIriIfNotImportOrAxiom =
    (arbitraryLookaheadOption [parseDirectlyImportsDocument] >> never) <|>
    optionMaybe iriCurie

parseEntity' :: EntityType -> String -> CharParser st Entity
parseEntity' t k = parseEnclosedWithKeyword k $ do
    iri <- iriCurie
    return $ mkEntity t iri

parseEntity :: CharParser st Entity
parseEntity =
    parseEntity' Class "Class" <|?>
    parseEntity' Datatype "Datatype" <|?>
    parseEntity' ObjectProperty "ObjectProperty" <|?>
    parseEntity' DataProperty "DataProperty" <|?>
    parseEntity' NamedIndividual "NamedIndividual"

{- # Axioms
## Declaration -}

parseDeclaration :: CharParser st Axiom
parseDeclaration = parseEnclosedWithKeyword "Declaration" $ do
    annotations <- many (parseAnnotation << skips)
    skips
    entity <- parseEntity
    return $ Declaration annotations entity

-- ## ClassExpression

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
parseObjectProperty = ObjectProp <$> iriCurie

parseInverseObjectProperty :: CharParser st ObjectPropertyExpression
parseInverseObjectProperty = parseEnclosedWithKeyword "ObjectInverseOf" $
    ObjectInverseOf <$> parseObjectProperty

parseObjectPropertyExpression :: CharParser st ObjectPropertyExpression
parseObjectPropertyExpression =
    parseInverseObjectProperty <|?>
    parseObjectProperty


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
    (iriCurie << skips) <*>
    (parseLiteral)

parseDatatypeRestriction :: CharParser st DataRange
parseDatatypeRestriction = parseEnclosedWithKeyword "DatatypeRestriction" $ do
    dataType <- iriCurie
    skips
    restrictions <- many1Skip parseDatatypeResComponent
    return $ DataTypeRest dataType restrictions

parseDataRange :: CharParser st DataRange
parseDataRange =
    parseDataJunction <|?>
    parseDataComplementOf <|?>
    parseDataOneOf <|?>
    parseDatatypeRestriction <|?>
    DataType <$> iriCurie

parseDataCardinality :: CharParser st ClassExpression
parseDataCardinality = DataCardinality <$> (
        cardinality "DataMinCardinality" MinCardinality <|?>
        cardinality "DataMaxCardinality" MaxCardinality <|?>
        cardinality "DataExactCardinality" ExactCardinality
    )
    where cardinality s t = (parseCardinality' t s a b)
          a = iriCurie
          b = parseDataRange

parseDataSomeValuesFrom :: CharParser st ClassExpression
parseDataSomeValuesFrom = parseEnclosedWithKeyword "DataSomeValuesFrom" $
    DataValuesFrom SomeValuesFrom <$> many1Skip iriCurie <*> parseDataRange

parseDataAllValuesFrom :: CharParser st ClassExpression
parseDataAllValuesFrom = parseEnclosedWithKeyword "DataAllValuesFrom" $
    DataValuesFrom AllValuesFrom <$> many1Skip iriCurie <*> parseDataRange

parseDataHasValue :: CharParser st ClassExpression
parseDataHasValue = parseEnclosedWithKeyword "DataHasValue" $
    DataHasValue <$> iriCurie <*> parseLiteral


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

    (Expression <$> iriCurie)

-- ## SubClassOf

parseSubClassOf :: CharParser st ClassAxiom
parseSubClassOf = parseEnclosedWithKeyword "SubClassOf" $ do
    annotations <- manySkip parseAnnotation
    skips
    subClassExpression <- parseClassExpression
    skips
    superClassExpression <- parseClassExpression
    return $ SubClassOf annotations subClassExpression superClassExpression

-- ## EquivalentClasses

parseEquivalentClasses :: CharParser st ClassAxiom
parseEquivalentClasses = parseEnclosedWithKeyword "EquivalentClasses" $
    EquivalentClasses <$> parseAnnotations <*> manyNSkip 2 parseClassExpression

-- ## DisjointUnion

parseDisjointUnion :: CharParser st ClassAxiom
parseDisjointUnion = parseEnclosedWithKeyword "DisjointUnion" $
    DisjointUnion <$>
    parseAnnotations <*>
    (iriCurie << skips) <*>
    manyNSkip 2 parseClassExpression

parseClassAxiom :: CharParser st Axiom
parseClassAxiom = ClassAxiom_ <$> (
        parseSubClassOf <|?>
        parseEquivalentClasses <|?>
        parseDisjointUnion
    )

parseAxiom :: CharParser st Axiom
parseAxiom = try parseDeclaration <|> try parseClassAxiom


parseOntology :: CharParser st Ontology
parseOntology = parseEnclosedWithKeyword "Ontology" $ do
    ontologyIri <- parseIriIfNotImportOrAxiom
    skips
    versionIri <- parseIriIfNotImportOrAxiom
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
    (skips >> parseOntology)


-- ** TESTING PURPOSES ONLY **
pta :: IO ()
pta = do
    files <- getDirectoryContents "./OWL2/tests"
    let fs = filter (isSuffixOf ".ofn") files
    foldr (\ f p -> do
            p
            putStr ("Testing " ++ f ++ "...")
            content <- readFile ("./OWL2/tests/" ++ f)
            let res = parse parseOntologyDocument f content
            putStrLn $ either (const "Failed") (const "Success") res
        ) (return ()) fs
    return ()

pt :: IO ()
pt = do
    content <- readFile "./test.ofn"
    parseTest parseOntologyDocument content
    return ()
