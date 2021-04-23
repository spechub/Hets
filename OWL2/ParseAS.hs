{-# LANGUAGE TupleSections #-}

module OWL2.ParserAS where

import OWL2.AS

import Common.AnnoParser (newlineOrEof)
import Common.IRI
import Common.Parsec

import Text.ParserCombinators.Parsec

import Data.Char

-- | parses a comment
comment :: CharParser st String
comment = try $ do
    char '#'
    manyTill anyChar newlineOrEof

atLeast :: Int -> CharParser st a -> CharParser st [a]
atLeast n p = foldr (\ _ r -> p <:> r) (return []) [1 .. n] <++> many p

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
parseAnonymousIndividual = return "TODO"


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
parseLiteral = try parseTypedLiteral <|> try parseUntypedLiteral

parseAnnotationValue :: CharParser st AnnotationValue
parseAnnotationValue =
    try (parseLiteral >>= return . AnnValLit) <|>
    try (iriCurie >>= return . AnnValue) <|>
    try (parseAnonymousIndividual >>= return . AnnAnInd)

parseAnnotation :: CharParser st Annotation
parseAnnotation = parseEnclosedWithKeyword "Annotation" $ do
    an <- (many (try parseAnnotation) << skips)
    skips
    property <- iriCurie
    skips
    value <- parseAnnotationValue
    return $ Annotation an property value

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
    parseEntity' Class "Class" <|>
    parseEntity' Datatype "Datatype" <|>
    parseEntity' ObjectProperty "ObjectProperty" <|>
    parseEntity' DataProperty "DataProperty" <|>
    parseEntity' NamedIndividual "NamedIndividual"

parseDeclaration :: CharParser st Axiom
parseDeclaration = parseEnclosedWithKeyword "Declaration" $ do
    annotations <- many (parseAnnotation << skips)
    skips
    entity <- parseEntity
    return $ Declaration annotations entity


parseObjectIntersectionOf :: CharParser st ClassExpression
parseObjectIntersectionOf = parseEnclosedWithKeyword "ObjectIntersectionOf" $ do
    classes <- atLeast 2 (parseClassExpression << skips)
    return $ ObjectJunction IntersectionOf classes

parseObjectJunction :: CharParser st ClassExpression
parseObjectJunction = parseObjectIntersectionOf

parseClassExpression :: CharParser st ClassExpression
parseClassExpression =
    try parseObjectJunction <|>
    (Expression <$> try iriCurie)

parseSubClassOf :: CharParser st ClassAxiom
parseSubClassOf = parseEnclosedWithKeyword "SubClassOf" $ do
    annotations <- (many parseAnnotation << skips)
    skips
    subClassExpression <- parseClassExpression
    skips
    superClassExpression <- parseClassExpression
    return $ SubClassOf annotations subClassExpression superClassExpression


parseClassAxiom :: CharParser st Axiom
parseClassAxiom = ClassAxiom_ <$> parseSubClassOf

parseAxiom :: CharParser st Axiom
parseAxiom = try parseDeclaration <|> try parseClassAxiom


parseOntology :: CharParser st Ontology
parseOntology = parseEnclosedWithKeyword "Ontology" $ do
    ontologyIri <- parseIriIfNotImportOrAxiom
    skips
    versionIri <- parseIriIfNotImportOrAxiom
    skips
    imports <- many (parseDirectlyImportsDocument << skips)
    skips
    annotations <- many (parseAnnotation << skips)
    skips
    axioms <- many (parseAxiom << skips)
    return $ Ontology ontologyIri versionIri (imports) annotations axioms


-- | Parses an OntologyDocument from Owl2 Functional Syntax
parseOntologyDocument :: CharParser st OntologyDocument
parseOntologyDocument = do
    prefixes <- many (parsePrefixDeclaration << skips)
    skips
    ontology <- parseOntology
    return $ OntologyDocument prefixes ontology


pt :: IO ()
pt = do
    content <- readFile "./test.ofn"
    parseTest parseOntologyDocument content
    return ()
