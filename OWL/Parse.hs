{- |
Module      :  $Header$
Description :  Manchester syntax parser for OWL 1.1
Copyright   :  (c) DFKI GmbH, Uni Bremen 2007-2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Manchester syntax parser for OWL 1.1
<http://www.webont.org/owled/2008dc/papers/owled2008dc_paper_11.pdf>
<http://www.faqs.org/rfcs/rfc3987.html>
<http://www.faqs.org/rfcs/rfc4646.html>
-}

module OWL.Parse (basicSpec) where

import OWL.AS
import DL.DLKeywords (casl_dl_keywords)
import Common.Token (casl_reserved_words)
import Common.Lexer hiding (skip)

import Text.ParserCombinators.Parsec
import Data.Char

ncNameStart :: Char -> Bool
ncNameStart c = isAlpha c || c == '_'

-- | rfc3987 plus '+' from scheme (scheme does not allow the dots)
ncNameChar :: Char -> Bool
ncNameChar c = isAlphaNum c || elem c ".+-_\183"

prefix :: CharParser st String
prefix = satisfy ncNameStart <:> many (satisfy ncNameChar)

iunreserved :: Char -> Bool
iunreserved c = isAlphaNum c || elem c "-._~" || ord c >= 160 && ord c <= 55295

-- maybe lower case hex-digits should be illegal
pctEncoded :: CharParser st String
pctEncoded = char '%' <:> hexDigit <:> single hexDigit

-- | comma and parens removed!
subDelims :: Char -> Bool
subDelims c = elem c "!$&'*+;="

iunreservedSubDelims :: String -> CharParser st Char
iunreservedSubDelims cs =
    satisfy $ \ c -> iunreserved c || subDelims c || elem c cs

iunreservedPctEncodedSubDelims :: String -> CharParser st String
iunreservedPctEncodedSubDelims cs =
    single (iunreservedSubDelims cs) <|> pctEncoded

ipChar :: CharParser st String
ipChar = iunreservedPctEncodedSubDelims ":@"

ifragment :: CharParser st String
ifragment = flat $ many (ipChar <|> single (char '/' <|> char '?'))

iquery :: CharParser st String
iquery = ifragment -- ignore iprivate

iregName :: CharParser st String
iregName = flat $ many $ iunreservedPctEncodedSubDelims ""

iuserinfo :: CharParser st String
iuserinfo = flat $ many $ iunreservedPctEncodedSubDelims ":"

-- | parse zero or at most n consecutive arguments
atMost :: Int -> GenParser tok st a -> GenParser tok st [a]
atMost n p = if n <= 0 then return [] else
     p <:> atMost (n - 1) p <|> return []

-- | parse at least one but at most n conse
atMost1 :: Int -> GenParser tok st a -> GenParser tok st [a]
atMost1 n p = p <:> atMost (n - 1) p

decOctet :: CharParser st String
decOctet = atMost 3 digit
  `checkWith` \ s -> let v = value 10 s in v <= 255 &&
                             (if v == 0 then s == "0" else take 1 s /= "0")

iPv4Adress :: CharParser st String
iPv4Adress = decOctet <++> string "."
  <++> decOctet <++> string "."
  <++> decOctet <++> string "."
  <++> decOctet

ihost :: CharParser st String
ihost = iregName <|> iPv4Adress -- or ipLiteral

port :: CharParser st String
port = many digit

iauthority :: CharParser st String
iauthority = option "" (try $ iuserinfo <++> string "@") <++> ihost
    <++> option "" (char ':' <:> port)

isegment :: CharParser st String
isegment = flat $ many ipChar

isegmentNz :: CharParser st String
isegmentNz = flat $ many1 ipChar

ipathAbempty :: CharParser st String
ipathAbempty = flat $ many (char '/' <:> isegment)

ipathAbsolute :: CharParser st String
ipathAbsolute = char '/' <:> option "" (isegmentNz <++> ipathAbempty)

ipathRootless :: CharParser st String
ipathRootless = isegmentNz <++> ipathAbempty

-- added comma and parens here
ipathEmpty :: CharParser st String
ipathEmpty = notFollowedBy (iunreservedSubDelims ":@%(), ") >> return ""

iauthorityWithPath :: CharParser st String
iauthorityWithPath = try (string "//") <++> iauthority <++> ipathAbempty

optQueryOrFrag :: CharParser st String
optQueryOrFrag = option "" (char '?' <:> iquery)
  <++> option "" (char '#' <:> ifragment)

-- | covers irelative-part (therefore we omit curie)
ihierPart :: CharParser st String
ihierPart =
  iauthorityWithPath <|> ipathAbsolute <|> ipathRootless <|> ipathEmpty

hierPartWithOpts :: CharParser st String
hierPartWithOpts = ihierPart <++> optQueryOrFrag

skip :: CharParser st a -> CharParser st a
skip = (<< spaces)

uriQ :: CharParser st QName
uriQ = do
    pre <- try (prefix << char ':')
    r <- hierPartWithOpts
    return $ QN pre r ""
  <|> fmap mkQName hierPartWithOpts

datatypeKeys :: [String]
datatypeKeys = ["integer", "decimal", "float", "string"]

uriP :: CharParser st QName
uriP = skip $ checkWith uriQ $ \ q -> not $ elem q
  $ map mkQName $ datatypeKeys ++ casl_reserved_words ++ casl_dl_keywords

datatypeUri :: CharParser st QName
datatypeUri = fmap mkQName (choice $ map keyword datatypeKeys) <|> uriP

stringLit :: CharParser st String
stringLit = enclosedBy (flat $ many $ single (noneOf "\\\"")
                        <|> char '\\' <:> single anyChar) $ char '\"'

optSign :: CharParser st String
optSign = option "" (single $ oneOf "+-")

postDecimal :: CharParser st String
postDecimal = char '.' <:> getNumber

fullDecimal :: CharParser st String
fullDecimal = getNumber <++> option "" postDecimal

decimalLit :: CharParser st String
decimalLit = optSign <++> fullDecimal

floatingPointLit :: CharParser st String
floatingPointLit = optSign <++> (fullDecimal <|> postDecimal)
  <++> option "" (oneOf "eE" <:> optSign <++> getNumber)
  <++> single (oneOf "fF")

languageTag :: CharParser st String
languageTag = atMost1 4 letter
  <++> flat (many $ char '-' <:> atMost1 8 alphaNum)

stringConstant :: CharParser st Constant
stringConstant = do
  s <- stringLit
  do  string "^^"
      d <- datatypeUri
      return $ Constant s $ Typed d
    <|> do
      char '@'
      t <- skip languageTag
      return $ Constant s $ Untyped t
    <|> skip (return $ Constant s $ Typed $ mkQName "string")

constant :: CharParser st Constant
constant = do
    f <- skip $ try floatingPointLit
    return $ Constant f $ Typed $ mkQName "float"
  <|> do
    d <- skip decimalLit
    return $ Constant d $ Typed $ mkQName
      $ if any (== '.') d then "decimal" else "integer"
  <|> stringConstant

-- * description

owlClassUri :: CharParser st QName
owlClassUri = uriP

individualUri :: CharParser st QName
individualUri = uriP

parensP :: CharParser st a -> CharParser st a
parensP = between (skip $ char '(') (skip $ char ')')

bracesP :: CharParser st a -> CharParser st a
bracesP = between (skip $ char '{') (skip $ char '}')

bracketsP :: CharParser st a -> CharParser st a
bracketsP = between (skip $ char '[') (skip $ char ']')

commaP :: CharParser st ()
commaP = skip (char ',') >> return ()

sepByComma :: CharParser st a -> CharParser st [a]
sepByComma p = sepBy1 p commaP

-- | plain string parser with skip
pkeyword :: String -> CharParser st ()
pkeyword s = skip $ try (string s) >> return ()

keywordNotFollowedBy :: String -> CharParser st Char -> CharParser st String
keywordNotFollowedBy s c = skip $ try $ string s << notFollowedBy c

-- | keyword not followed by any alphanum
keyword :: String -> CharParser st String
keyword s = keywordNotFollowedBy s alphaNum

-- base OWLClass excluded
atomic :: CharParser st Description
atomic = parensP description
  <|> fmap ObjectOneOf (bracesP $ sepByComma individualUri)

objectPropertyExpr :: CharParser st ObjectPropertyExpression
objectPropertyExpr = do
    keyword "InverseOf"
    fmap InverseOp objectPropertyExpr
  <|> fmap OpURI uriP

showFacet :: DatatypeFacet -> String
showFacet df = case df of
    LENGTH -> "length"
    MINLENGTH -> "minLength"
    MAXLENGTH -> "maxLength"
    PATTERN -> "pattern"
    MININCLUSIVE -> "<="
    MINEXCLUSIVE -> "<"
    MAXINCLUSIVE -> ">="
    MAXEXCLUSIVE -> ">"
    TOTALDIGITS -> "digits"
    FRACTIONDIGITS -> "fraction"

facetValuePair :: CharParser st (DatatypeFacet, RestrictionValue)
facetValuePair = do
  df <- choice $ map (\ f -> keyword (showFacet f) >> return f)
      [ LENGTH
      , MINLENGTH
      , MAXLENGTH
      , PATTERN
      , TOTALDIGITS
      , FRACTIONDIGITS ] ++ map
      (\ f -> keywordNotFollowedBy (showFacet f) (oneOf "<>=")
              >> return f)
      [ MININCLUSIVE
      , MINEXCLUSIVE
      , MAXINCLUSIVE
      , MAXEXCLUSIVE ]
  rv <- constant
  return (df, rv)

dataRangeRestriction :: CharParser st DataRange
dataRangeRestriction = do
  d <- fmap DRDatatype datatypeUri
  option d $ fmap (DatatypeRestriction d) $ bracketsP
    $ sepByComma facetValuePair

dataRange :: CharParser st DataRange
dataRange = do
    keyword "not"
    fmap DataComplementOf dataRange
   <|> fmap DataOneOf (bracesP $ sepByComma constant)
   <|> dataRangeRestriction

someOrOnly :: CharParser st QuantifierType
someOrOnly = choice
  $ (keyword "has" >> return SomeValuesFrom)
  : map (\ f -> keyword (showQuantifierType f) >> return f)
    [AllValuesFrom, SomeValuesFrom]

card :: CharParser st (CardinalityType, Int)
card = do
  c <- choice $ map (\ f -> keywordNotFollowedBy (showCardinalityType f) letter
                            >> return f)
             [MinCardinality, MaxCardinality, ExactCardinality]
  n <- skip getNumber
  return (c, value 10 n)

individualOrConstant :: CharParser st (Either QName Constant)
individualOrConstant = fmap Left individualUri <|> fmap Right constant

individualOrConstantList :: CharParser st (Either [QName] [Constant])
individualOrConstantList = do
    ioc <- individualOrConstant
    case ioc of
      Left u -> fmap (Left . (u :)) $ option []
        $ commaP >> sepByComma individualUri
      Right c -> fmap (Right . (c :)) $ option []
        $ commaP >> sepByComma constant

primaryOrDataRange :: CharParser st (Either Description DataRange)
primaryOrDataRange = do
  ns <- many $ keyword "not"
  ed <- do
      u <- datatypeUri
      fmap Left (restrictionAny $ OpURI u)
        <|> fmap (Right . DatatypeRestriction (DRDatatype u))
            (bracketsP $ sepByComma facetValuePair)
        <|> return (if elem u $ map mkQName datatypeKeys
              then Right $ DRDatatype u
              else Left $ OWLClass u) -- could still be a datatypeUri
    <|> do
      e <- bracesP individualOrConstantList
      return $ case e of
        Left us -> Left $ ObjectOneOf us
        Right cs -> Right $ DataOneOf cs
    <|> fmap Left restrictionOrAtomic
  return $ if even (length ns) then ed else
    case ed of
      Left d -> Left $ ObjectComplementOf d
      Right d -> Right $ DataComplementOf d

restrictionAny :: ObjectPropertyExpression -> CharParser st Description
restrictionAny opExpr = do
      keyword "value"
      e <- individualOrConstant
      case e of
        Left u -> return $ ObjectHasValue opExpr u
        Right c -> case opExpr of
          OpURI dpExpr -> return $ DataHasValue dpExpr c
          _ -> unexpected "constant"
    <|> do
      keyword "Self"
      return $ ObjectExistsSelf opExpr
    <|> do
      keyword "onlysome"
      ds <- bracketsP $ sepByComma description
      let as = map (\ d -> ObjectValuesFrom SomeValuesFrom opExpr d) ds
          o = ObjectValuesFrom AllValuesFrom opExpr $ ObjectJunction UnionOf ds
      return $ ObjectJunction IntersectionOf $ o : as
    <|> do
      v <- someOrOnly
      pr <- primaryOrDataRange
      case pr of
        Left p -> return $ ObjectValuesFrom v opExpr p
        Right r -> case opExpr of
          OpURI dpExpr -> return $ DataValuesFrom v dpExpr [] r
          _ -> unexpected $ "dataRange after " ++ showQuantifierType v
    <|> do
      (c, n) <- card
      mp <- optionMaybe primaryOrDataRange
      case mp of
         Nothing -> return $ ObjectCardinality $ Cardinality c n opExpr Nothing
         Just pr -> case pr of
           Left p ->
             return $ ObjectCardinality $ Cardinality c n opExpr $ Just p
           Right r -> case opExpr of
             OpURI dpExpr ->
               return $ DataCardinality $ Cardinality c n dpExpr $ Just r
             _ -> unexpected $ "dataRange after " ++ showCardinalityType c

restriction :: CharParser st Description
restriction = objectPropertyExpr >>= restrictionAny

restrictionOrAtomic :: CharParser st Description
restrictionOrAtomic = do
    opExpr <- objectPropertyExpr
    restrictionAny opExpr <|> case opExpr of
       OpURI euri -> return $ OWLClass euri
       _ -> unexpected "inverse object property"
  <|> atomic

optNot :: (a -> a) -> CharParser st a  -> CharParser st a
optNot f p = (keyword "not" >> fmap f p) <|> p

primary :: CharParser st Description
primary = optNot ObjectComplementOf restrictionOrAtomic

conjunction :: CharParser st Description
conjunction = do
    curi <- fmap OWLClass $ try (owlClassUri << keyword "that")
    rs <- sepBy1 (optNot ObjectComplementOf restriction) $ keyword "and"
    return $ ObjectJunction IntersectionOf $ curi : rs
  <|> fmap (ObjectJunction IntersectionOf)
      (sepBy1 primary $ keyword "and")

description :: CharParser st Description
description = fmap (ObjectJunction UnionOf) $ sepBy1 conjunction $ keyword "or"

showEntityType :: EntityType -> String
showEntityType et = case et of
    OWLClassEntity -> "OWLClass"
    _ -> show et

entityType :: CharParser st EntityType
entityType = choice $ map (\ f -> keyword (showEntityType f) >> return f)
  [ Datatype
  , OWLClassEntity
  , ObjectProperty
  , DataProperty
  , Individual ]
-- AnnotationProperty is missing

entity :: CharParser st Entity
entity = do
  t <- entityType
  u <- parensP uriP
  return $ Entity t u

annotation :: CharParser st Annotation
annotation = do
  a <- uriP
  parensP $ do
      c <- constant
      return $ ExplicitAnnotation a c
    <|> do
      e <- entity
      return $ Annotation a e
    <|> do
      individualUri
      fail "unsupported individualURI of annotation"

-- | keyword followed by a colon (that is consumed too)
ckeyword :: String -> CharParser st ()
ckeyword s = pkeyword $ s ++ ":"

optAnnos :: CharParser st a -> CharParser st ([Annotation], a)
optAnnos p = do
  as <- option [] annotations
  a <- p
  return (as, a)

annotations :: CharParser st [Annotation]
annotations = do
  ckeyword "Annotations"
  as <- sepByComma $ optAnnos annotation
  return $ map snd as -- annoted annotations not supported yet

descriptionAnnotatedList :: CharParser st [([Annotation], Description)]
descriptionAnnotatedList = sepByComma $ optAnnos description

equivOrDisjoint :: CharParser st EquivOrDisjoint
equivOrDisjoint = choice
  $ map (\ f -> pkeyword (showEquivOrDisjoint f) >> return f)
  [Equivalent, Disjoint]

entityAnnos :: QName -> EntityType -> CharParser st [Axiom]
entityAnnos qn ty = do
    as <- annotations
    return [PlainAxiom as $ Declaration $ Entity ty qn]

classFrameBit :: QName -> CharParser st [Axiom]
classFrameBit curi = let duri = OWLClass curi in do
    entityAnnos curi OWLClassEntity
  <|> do
    ckeyword "SubclassOf"
    ds <- descriptionAnnotatedList
    return $ map (\ (as, d) -> PlainAxiom as $ SubClassOf duri d) ds
  <|> do
    e <- equivOrDisjoint
    ds <- descriptionAnnotatedList
    return [PlainAxiom (concatMap fst ds)
           $ EquivOrDisjointClasses e $ duri : map snd ds]
  <|> do
    ckeyword "DisjointUnionOf"
    as <- annotations
    ds <- sepByComma description
    return [PlainAxiom as $ DisjointUnion curi ds]
  <|> do
    ckeyword "Paraphrase"
    skip stringLit
    return []

classFrame :: CharParser st [Axiom]
classFrame = do
  ckeyword "Class"
  curi <- owlClassUri
  las <- many $ classFrameBit curi
  let as = concat las
  return $ if null as
    then [PlainAxiom [] $ Declaration $ Entity OWLClassEntity curi]
    else as

domainOrRange :: CharParser st ObjDomainOrRange
domainOrRange = choice
  $ map (\ f -> pkeyword (showObjDomainOrRange f) >> return f)
  [ObjDomain, ObjRange]

objectPropertyCharacter :: CharParser st Character
objectPropertyCharacter = choice
  $ map (\ f -> keyword (show f) >> return f)
  [ Functional
  , InverseFunctional
  , Reflexive
  , Irreflexive
  , Symmetric
  , Asymmetric
  , Transitive ]

objPropExprAList :: CharParser st [([Annotation], ObjectPropertyExpression)]
objPropExprAList = sepByComma $ optAnnos objectPropertyExpr

subPropertyKey :: CharParser st ()
subPropertyKey = ckeyword "SubPropertyOf"

characterKey :: CharParser st ()
characterKey = ckeyword "Characteristics"

objectFrameBit :: QName -> CharParser st [Axiom]
objectFrameBit ouri = let opExp = OpURI ouri in do
    entityAnnos ouri ObjectProperty
  <|> do
    r <- domainOrRange
    ds <- descriptionAnnotatedList
    return $ map (\ (as, d) -> PlainAxiom as
      $ ObjectPropertyDomainOrRange r opExp d) ds
  <|> do
    characterKey
    ds <- sepByComma $ optAnnos objectPropertyCharacter
    return $ map (\ (as, c) -> PlainAxiom as
      $ ObjectPropertyCharacter c opExp) ds
  <|> do
    subPropertyKey
    ds <- objPropExprAList
    return $ map (\ (as, s) -> PlainAxiom as
      $ SubObjectPropertyOf (OPExpression s) opExp) ds
  <|> do
    e <- equivOrDisjoint
    ds <- objPropExprAList
    return [PlainAxiom (concatMap fst ds)
           $ EquivOrDisjointObjectProperties e $ opExp : map snd ds]
  <|> do
    ckeyword "Inverses"
    ds <- objPropExprAList
    return $ map (\ (as, i) -> PlainAxiom as
      $ InverseObjectProperties opExp i) ds
  <|> do
    ckeyword "SubPropertyChain"
    as <- annotations
    os <- sepBy1 objectPropertyExpr (keyword "o")
    return [PlainAxiom as
      $ SubObjectPropertyOf (SubObjectPropertyChain os) opExp]

objectPropertyFrame :: CharParser st [Axiom]
objectPropertyFrame = do
  ckeyword "ObjectProperty"
  ouri <- uriP
  flat $ many $ objectFrameBit ouri

dataPropExprAList :: CharParser st [([Annotation], DataPropertyExpression)]
dataPropExprAList = sepByComma $ optAnnos uriP

dataFrameBit :: QName -> CharParser st [Axiom]
dataFrameBit duri = do
    entityAnnos duri DataProperty
  <|> do
    ckeyword "Domain"
    ds <- descriptionAnnotatedList
    return $ map (\ (as, d) -> PlainAxiom as
      $ DataPropertyDomainOrRange (DataDomain d) duri) ds
  <|> do
    ckeyword "Range"
    ds <- sepByComma $ optAnnos dataRange
    return $ map (\ (as, r) -> PlainAxiom as
      $ DataPropertyDomainOrRange (DataRange r) duri) ds
  <|> do
    characterKey
    as <- annotations
    keyword "Functional"
    return [PlainAxiom as $ FunctionalDataProperty duri]
  <|> do
    subPropertyKey
    ds <- dataPropExprAList
    return $ map (\ (as, s) -> PlainAxiom as $ SubDataPropertyOf s duri) ds
  <|> do
    e <- equivOrDisjoint
    ds <- dataPropExprAList
    return [PlainAxiom (concatMap fst ds)
           $ EquivOrDisjointDataProperties e $ duri : map snd ds]

dataPropertyFrame :: CharParser st [Axiom]
dataPropertyFrame = do
  ckeyword "DataProperty"
  duri <- uriP
  flat $ many $ dataFrameBit duri

sameOrDifferent :: CharParser st SameOrDifferent
sameOrDifferent = choice
  $ map (\ f -> pkeyword (showSameOrDifferent f) >> return f)
  [Same, Different]

fact :: QName -> CharParser st PlainAxiom
fact iuri = do
  pn <- option Positive $ keyword "not" >> return Negative
  u <- uriP
  do  c <- constant
      return $ DataPropertyAssertion $ Assertion u pn iuri c
    <|> do
      t <- individualUri
      return $ ObjectPropertyAssertion $ Assertion (OpURI u) pn iuri t

iFrameBit :: QName -> CharParser st [Axiom]
iFrameBit iuri = do
    entityAnnos iuri Individual
  <|> do
    ckeyword "Types"
    ds <- descriptionAnnotatedList
    return $ map (\ (as, d) -> PlainAxiom as $ ClassAssertion iuri d) ds
  <|> do
    s <- sameOrDifferent
    is <- sepByComma $ optAnnos individualUri
    return [PlainAxiom (concatMap fst is)
      $ SameOrDifferentIndividual s $ iuri : map snd is]
  <|> do
    ckeyword "Facts"
    fs <- sepByComma $ optAnnos $ fact iuri
    return $ map (\ (as, f) -> PlainAxiom as f) fs

individualFrame :: CharParser st [Axiom]
individualFrame = do
  ckeyword "Individual"
  iuri <- individualUri
  flat $ many $ iFrameBit iuri

equivOrDisjointKeyword :: String -> CharParser st EquivOrDisjoint
equivOrDisjointKeyword ext =
  (ckeyword ("Equivalent" ++ ext) >> return Equivalent)
  <|> (ckeyword ("Disjoint" ++ ext) >> return Disjoint)

-- note the plural when different
sameOrDifferentIndu :: CharParser st SameOrDifferent
sameOrDifferentIndu =
  (ckeyword "SameIndividual" >> return Same)
  <|> (ckeyword "DifferentIndividuals" >> return Different)

misc :: CharParser st Axiom
misc = do
    e <- equivOrDisjointKeyword "Classes"
    as <- annotations
    ds <- sepByComma description
    return $ PlainAxiom as $ EquivOrDisjointClasses e ds
  <|> do
    e <- equivOrDisjointKeyword "ObjectProperties"
    as <- annotations
    es <- sepByComma objectPropertyExpr
    return $ PlainAxiom as $ EquivOrDisjointObjectProperties e es
  <|> do
    e <- equivOrDisjointKeyword "DataProperties"
    as <- annotations
    ds <- sepByComma uriP
    return $ PlainAxiom as $ EquivOrDisjointDataProperties e ds
  <|> do
    s <- sameOrDifferentIndu
    as <- annotations
    is <- sepByComma individualUri
    return $ PlainAxiom as $ SameOrDifferentIndividual s is

frames :: CharParser st [Axiom]
frames = flat $ many $ classFrame
  <|> objectPropertyFrame <|> dataPropertyFrame <|> individualFrame
  <|> single misc

basicSpec :: CharParser st OntologyFile
basicSpec = do
  as <- frames
  return emptyOntologyFile { ontology = emptyOntology { axiomsList = as } }
