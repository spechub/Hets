{- |
Module      :  $Header$
Description :  Manchester syntax parser for OWL 2
Copyright   :  (c) DFKI GmbH, Uni Bremen 2007-2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Manchester syntax parser for OWL 2
<http://www.w3.org/TR/2009/NOTE-owl2-manchester-syntax-20091027/>
adpated from
Manchester syntax parser for OWL 1.1
<http://www.webont.org/owled/2008dc/papers/owled2008dc_paper_11.pdf>
<http://www.faqs.org/rfcs/rfc3987.html>
<http://www.faqs.org/rfcs/rfc4646.html>
-}

module OWL.Parse (basicSpec, symbItems, symbMapItems) where

import OWL.AS
import OWL.Keywords
import OWL.ColonKeywords

import Common.Keywords
import Common.Lexer
import Common.Parsec
import Common.AnnoParser (commentLine)
import Common.Utils (nubOrd)

import Text.ParserCombinators.Parsec
import Data.Char
import qualified Data.Map as Map

characters :: [Character]
characters = [minBound .. maxBound]

owlKeywords :: [String]
owlKeywords = notS : stringS : map show entityTypes
  ++ map show characters ++ keywords

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

-- comma and parens are removed here
-- but would cause no problems for full IRIs within angle brackets
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
iauthority = optionL (try $ iuserinfo <++> string "@") <++> ihost
    <++> optionL (char ':' <:> port)

isegment :: CharParser st String
isegment = flat $ many ipChar

isegmentNz :: CharParser st String
isegmentNz = flat $ many1 ipChar

ipathAbempty :: CharParser st String
ipathAbempty = flat $ many (char '/' <:> isegment)

ipathAbsolute :: CharParser st String
ipathAbsolute = char '/' <:> optionL (isegmentNz <++> ipathAbempty)

-- within abbreviated IRIs only ipath-noscheme should be used
-- that excludes colons via isegment-nz-nc
ipathRootless :: CharParser st String
ipathRootless = isegmentNz <++> ipathAbempty

iauthorityWithPath :: CharParser st String
iauthorityWithPath = tryString "//" <++> iauthority <++> ipathAbempty

optQueryOrFrag :: CharParser st String
optQueryOrFrag = optionL (char '?' <:> iquery)
  <++> optionL (char '#' <:> ifragment)

-- | covers irelative-part (therefore we omit curie)
ihierPart :: CharParser st String
ihierPart =
  iauthorityWithPath <|> ipathAbsolute <|> ipathRootless

hierPartWithOpts :: CharParser st String
hierPartWithOpts = ihierPart <++> optQueryOrFrag

skips :: CharParser st a -> CharParser st a
skips = (<< skipMany
        (forget space <|> forget commentLine <|> nestCommentOut <?> ""))

abbrIri :: CharParser st QName
abbrIri = try $ do
    pre <- try $ prefix << char ':'
    r <- hierPartWithOpts
    return $ QN pre r False ""
  <|> fmap mkQName hierPartWithOpts

fullIri :: CharParser st QName
fullIri = do
    char '<'
    QN pre r _ _ <- abbrIri
    char '>'
    return $ QN pre r True ""

uriQ :: CharParser st QName
uriQ = fullIri <|> abbrIri

-- boolean not documented
datatypeKeys :: [String]
datatypeKeys =
  [ booleanS
  , dATAS
  , decimalS
  , floatS
  , integerS
  , negativeIntegerS
  , nonNegativeIntegerS
  , nonPositiveIntegerS
  , positiveIntegerS
  , stringS
  , universalS
  ]

uriP :: CharParser st QName
uriP =
  skips $ checkWithUsing showQN uriQ $ \ q -> let p = namePrefix q in
  if null p then notElem (localPart q) owlKeywords
   else notElem p
     $ map (takeWhile (/= ':')) colonKeywords

-- | parse a possibly kinded list of comma separated uris aka symbols
symbItems :: GenParser Char st SymbItems
symbItems = do
  m <- optionMaybe entityType
  uris <- symbs
  return $ SymbItems m uris

-- | parse a comma separated list of uris
symbs :: GenParser Char st [URI]
symbs = uriP >>= \ u -> do
    commaP `followedWith` uriP
    us <- symbs
    return $ u : us
  <|> return [u]

-- | parse a possibly kinded list of comma separated symbol pairs
symbMapItems :: GenParser Char st SymbMapItems
symbMapItems = do
  m <- optionMaybe entityType
  uris <- symbPairs
  return $ SymbMapItems m uris

-- | parse a comma separated list of uri pairs
symbPairs :: GenParser Char st [(URI, Maybe URI)]
symbPairs = uriPair >>= \ u -> do
    commaP `followedWith` uriP
    us <- symbPairs
    return $ u : us
  <|> return [u]

uriPair :: GenParser Char st (URI, Maybe URI)
uriPair = uriP >>= \ u -> do
    pToken $ toKey mapsTo
    u2 <- uriP
    return (u, Just u2)
  <|> return (u, Nothing)

datatypeUri :: CharParser st QName
datatypeUri = fmap mkQName (choice $ map keyword datatypeKeys) <|> uriP

stringLit :: CharParser st String
stringLit = enclosedBy (flat $ many $ single (noneOf "\\\"")
                        <|> char '\\' <:> single anyChar) $ char '\"'

optSign :: CharParser st String
optSign = optionL (single $ oneOf "+-")

postDecimal :: CharParser st String
postDecimal = char '.' <:> getNumber

fullDecimal :: CharParser st String
fullDecimal = getNumber <++> optionL postDecimal

decimalLit :: CharParser st String
decimalLit = optSign <++> fullDecimal

floatingPointLit :: CharParser st String
floatingPointLit = optSign <++> (fullDecimal <|> postDecimal)
  <++> optionL (oneOf "eE" <:> optSign <++> getNumber)
  << oneOf "fF"

languageTag :: CharParser st String
languageTag = atMost1 4 letter
  <++> flat (many $ char '-' <:> atMost1 8 alphaNum)

stringConstant :: CharParser st Constant
stringConstant = do
  s <- stringLit
  do
      string cTypeS
      d <- datatypeUri
      return $ Constant s $ Typed d
    <|> do
      string asP
      t <- skips languageTag
      return $ Constant s $ Untyped t
    <|> skips (return $ Constant s $ Typed $ mkQName stringS)

constant :: CharParser st Constant
constant = do
    f <- skips $ try floatingPointLit
    return $ Constant f $ Typed $ mkQName floatS
  <|> do
    d <- skips decimalLit
    return $ Constant d $ Typed $ mkQName
      $ if any (== '.') d then decimalS else integerS
  <|> stringConstant

-- * description

owlClassUri :: CharParser st QName
owlClassUri = uriP

individualUri :: CharParser st QName
individualUri = uriP

skipChar :: Char -> CharParser st ()
skipChar = forget . skips . char

parensP :: CharParser st a -> CharParser st a
parensP = between (skipChar '(') (skipChar ')')

bracesP :: CharParser st a -> CharParser st a
bracesP = between (skipChar '{') (skipChar '}')

bracketsP :: CharParser st a -> CharParser st a
bracketsP = between (skipChar '[') (skipChar ']')

commaP :: CharParser st ()
commaP = skipChar ',' >> return ()

sepByComma :: CharParser st a -> CharParser st [a]
sepByComma p = sepBy1 p commaP

-- keywords need to be case insensitive

-- | parse character case insensitive
ichar :: Char -> CharParser st Char
ichar c = char (toUpper c) <|> char (toLower c) <?> show [c]

-- | parse string case insensitive
istring :: String -> CharParser st String
istring s = case s of
  [] -> return ""
  c : r -> ichar c <:> istring r

-- | plain string parser with skip
pkeyword :: String -> CharParser st ()
pkeyword s = keywordNotFollowedBy s (alphaNum <|> char '/') >> return ()

keywordNotFollowedBy :: String -> CharParser st Char -> CharParser st String
keywordNotFollowedBy s c = skips $ try $ istring s << notFollowedBy c

-- | keyword not followed by any alphanum
keyword :: String -> CharParser st String
keyword s = keywordNotFollowedBy s alphaNum

-- base OWLClass excluded
atomic :: CharParser st Description
atomic = parensP description
  <|> fmap ObjectOneOf (bracesP $ sepByComma individualUri)

objectPropertyExpr :: CharParser st ObjectPropertyExpression
objectPropertyExpr = do
    keyword inverseOfS
    fmap InverseOp objectPropertyExpr
  <|> fmap OpURI uriP

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
    keyword notS
    fmap DataComplementOf dataRange
   <|> fmap DataOneOf (bracesP $ sepByComma constant)
   <|> dataRangeRestriction

someOrOnly :: CharParser st QuantifierType
someOrOnly = choice
  $ map (\ f -> keyword (showQuantifierType f) >> return f)
    [AllValuesFrom, SomeValuesFrom]

card :: CharParser st (CardinalityType, Int)
card = do
  c <- choice $ map (\ f -> keywordNotFollowedBy (showCardinalityType f) letter
                            >> return f)
             [MinCardinality, MaxCardinality, ExactCardinality]
  n <- skips getNumber
  return (c, value 10 n)

individualOrConstant :: CharParser st (Either QName Constant)
individualOrConstant = fmap Right constant <|> fmap Left individualUri

individualOrConstantList :: CharParser st (Either [QName] [Constant])
individualOrConstantList = do
    ioc <- individualOrConstant
    case ioc of
      Left u -> fmap (Left . (u :)) $ optionL
        $ commaP >> sepByComma individualUri
      Right c -> fmap (Right . (c :)) $ optionL
        $ commaP >> sepByComma constant

primaryOrDataRange :: CharParser st (Either Description DataRange)
primaryOrDataRange = do
  ns <- many $ keyword notS  -- allows multiple not before primary
  ed <- do
      u <- datatypeUri
      fmap Left (restrictionAny $ OpURI u)
        <|> fmap (Right . DatatypeRestriction (DRDatatype u))
            (bracketsP $ sepByComma facetValuePair)
        <|> return (if elem (localPart u) datatypeKeys
                       && elem (namePrefix u) ["", "xsd"]
              then Right $ DRDatatype u
              else Left $ OWLClassDescription u) -- could still be a datatypeUri
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

mkObjectJunction :: JunctionType -> [Description] -> Description
mkObjectJunction ty ds = case nubOrd ds of
  [] -> error "mkObjectJunction"
  [x] -> x
  ns -> ObjectJunction ty ns

restrictionAny :: ObjectPropertyExpression -> CharParser st Description
restrictionAny opExpr = do
      keyword valueS
      e <- individualOrConstant
      case e of
        Left u -> return $ ObjectHasValue opExpr u
        Right c -> case opExpr of
          OpURI dpExpr -> return $ DataHasValue dpExpr c
          _ -> unexpected "constant"
    <|> do
      keyword selfS
      return $ ObjectExistsSelf opExpr
    <|> do -- sugar
      keyword onlysomeS
      ds <- bracketsP $ sepByComma description
      let as = map (ObjectValuesFrom SomeValuesFrom opExpr) ds
          o = ObjectValuesFrom AllValuesFrom opExpr
              $ mkObjectJunction UnionOf ds
      return $ mkObjectJunction IntersectionOf $ o : as
    <|> do -- sugar
      keyword hasS
      iu <- individualUri
      return $ ObjectValuesFrom SomeValuesFrom opExpr $ ObjectOneOf [iu]
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
       OpURI euri -> return $ OWLClassDescription euri
       _ -> unexpected "inverse object property"
  <|> atomic

optNot :: (a -> a) -> CharParser st a -> CharParser st a
optNot f p = (keyword notS >> fmap f p) <|> p

primary :: CharParser st Description
primary = optNot ObjectComplementOf restrictionOrAtomic

conjunction :: CharParser st Description
conjunction = do
    curi <- fmap OWLClassDescription $ try (owlClassUri << keyword thatS)
    rs <- sepBy1 (optNot ObjectComplementOf restriction) $ keyword andS
    return $ mkObjectJunction IntersectionOf $ curi : rs
  <|> fmap (mkObjectJunction IntersectionOf)
      (sepBy1 primary $ keyword andS)

description :: CharParser st Description
description =
  fmap (mkObjectJunction UnionOf) $ sepBy1 conjunction $ keyword orS

entityType :: CharParser st EntityType
entityType = choice $ map (\ f -> keyword (show f) >> return f)
  entityTypes

-- AnnotationProperty is missing

entity :: CharParser st Entity
entity = do
  t <- entityType
  u <- parensP uriP
  return $ Entity t u

annotation :: CharParser st Annotation
annotation = do
  a <- uriP
  do
      c <- constant
      return $ ExplicitAnnotation a c
    <|> do
      e <- entity
      return $ Annotation a e
    <|> do
      individualUri
      fail "unsupported individualURI of annotation"

optAnnos :: CharParser st a -> CharParser st ([Annotation], a)
optAnnos p = do
  as <- annotations
  a <- p
  return (as, a)

annotations :: CharParser st [Annotation]
annotations = optionL realAnnotations

realAnnotations :: CharParser st [Annotation]
realAnnotations = do
  pkeyword annotationsC
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
    as <- realAnnotations
    return [PlainAxiom as $ Declaration $ Entity ty qn]

classFrameBit :: QName -> CharParser st [Axiom]
classFrameBit curi = let duri = OWLClassDescription curi in
    entityAnnos curi Class
  <|> do
    pkeyword subClassOfC
    ds <- descriptionAnnotatedList
    return $ map (\ (as, d) -> PlainAxiom as $ SubClassOf duri d) ds
  <|> do
    e <- equivOrDisjoint
    ds <- descriptionAnnotatedList
    return [PlainAxiom (concatMap fst ds)
           $ EquivOrDisjointClasses e $ duri : map snd ds]
  <|> do
    pkeyword disjointUnionOfC
    as <- annotations
    ds <- sepByComma description
    return [PlainAxiom as $ DisjointUnion curi ds]

classFrame :: CharParser st [Axiom]
classFrame = do
  pkeyword classC
  curi <- owlClassUri
  as <- flat $ many $ classFrameBit curi
  return $ if null as
    then [PlainAxiom [] $ Declaration $ Entity Class curi]
    else as

domainOrRange :: CharParser st ObjDomainOrRange
domainOrRange = choice
  $ map (\ f -> pkeyword (showObjDomainOrRange f) >> return f)
  [ObjDomain, ObjRange]

objectPropertyCharacter :: CharParser st Character
objectPropertyCharacter =
  choice $ map (\ f -> keyword (show f) >> return f) characters

objPropExprAList :: CharParser st [([Annotation], ObjectPropertyExpression)]
objPropExprAList = sepByComma $ optAnnos objectPropertyExpr

subPropertyKey :: CharParser st ()
subPropertyKey = pkeyword subPropertyOfC

characterKey :: CharParser st ()
characterKey = pkeyword characteristicsC

objectFrameBit :: QName -> CharParser st [Axiom]
objectFrameBit ouri = let opExp = OpURI ouri in
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
    pkeyword inverseOfC
    ds <- objPropExprAList
    return $ map (\ (as, i) -> PlainAxiom as
      $ InverseObjectProperties opExp i) ds
  <|> do
    pkeyword subPropertyChainC
    as <- annotations
    os <- sepBy1 objectPropertyExpr (keyword oS)
    return [PlainAxiom as
      $ SubObjectPropertyOf (SubObjectPropertyChain os) opExp]

objectPropertyFrame :: CharParser st [Axiom]
objectPropertyFrame = do
  pkeyword objectPropertyC
  ouri <- uriP
  as <- flat $ many $ objectFrameBit ouri
  return $ if null as
    then [PlainAxiom [] $ Declaration $ Entity ObjectProperty ouri]
    else as

dataPropExprAList :: CharParser st [([Annotation], DataPropertyExpression)]
dataPropExprAList = sepByComma $ optAnnos uriP

dataFrameBit :: QName -> CharParser st [Axiom]
dataFrameBit duri =
    entityAnnos duri DataProperty
  <|> do
    pkeyword domainC
    ds <- descriptionAnnotatedList
    return $ map (\ (as, d) -> PlainAxiom as
      $ DataPropertyDomainOrRange (DataDomain d) duri) ds
  <|> do
    pkeyword rangeC
    ds <- sepByComma $ optAnnos dataRange
    return $ map (\ (as, r) -> PlainAxiom as
      $ DataPropertyDomainOrRange (DataRange r) duri) ds
  <|> do
    characterKey
    as <- annotations
    keyword functionalS
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
  pkeyword dataPropertyC
  duri <- uriP
  as <- flat $ many $ dataFrameBit duri
  return $ if null as
    then [PlainAxiom [] $ Declaration $ Entity DataProperty duri]
    else as

sameOrDifferent :: CharParser st SameOrDifferent
sameOrDifferent = choice
  $ map (\ f -> pkeyword (showSameOrDifferent f) >> return f)
  [Same, Different]

fact :: QName -> CharParser st PlainAxiom
fact iuri = do
  pn <- option Positive $ keyword notS >> return Negative
  u <- uriP
  do
      c <- constant
      return $ DataPropertyAssertion $ Assertion u pn iuri c
    <|> do
      t <- individualUri
      return $ ObjectPropertyAssertion $ Assertion (OpURI u) pn iuri t

iFrameBit :: QName -> CharParser st [Axiom]
iFrameBit iuri =
    entityAnnos iuri NamedIndividual
  <|> do
    pkeyword typesC
    ds <- descriptionAnnotatedList
    return $ map (\ (as, d) -> PlainAxiom as $ ClassAssertion iuri d) ds
  <|> do
    s <- sameOrDifferent
    is <- sepByComma $ optAnnos individualUri
    return [PlainAxiom (concatMap fst is)
      $ SameOrDifferentIndividual s $ iuri : map snd is]
  <|> do
    pkeyword factsC
    fs <- sepByComma $ optAnnos $ fact iuri
    return $ map (uncurry PlainAxiom) fs

individualFrame :: CharParser st [Axiom]
individualFrame = do
  pkeyword individualC
  iuri <- individualUri
  as <- flat $ many $ iFrameBit iuri
  return $ if null as
    then [PlainAxiom [] $ Declaration $ Entity NamedIndividual iuri]
    else as

equivOrDisjointKeyword :: String -> CharParser st EquivOrDisjoint
equivOrDisjointKeyword ext =
  (pkeyword ("Equivalent" ++ ext) >> return Equivalent)
  <|> (pkeyword ("Disjoint" ++ ext) >> return Disjoint)

-- note the plural when different
sameOrDifferentIndu :: CharParser st SameOrDifferent
sameOrDifferentIndu =
  (pkeyword sameIndividualC >> return Same)
  <|> (pkeyword differentIndividualsC >> return Different)

misc :: CharParser st Axiom
misc = do
    e <- equivOrDisjointKeyword classesC
    as <- annotations
    ds <- sepByComma description
    return $ PlainAxiom as $ EquivOrDisjointClasses e ds
  <|> do
    e <- equivOrDisjointKeyword propertiesC
    as <- annotations
    es <- sepByComma objectPropertyExpr
    -- indistinguishable from dataProperties
    return $ PlainAxiom as $ EquivOrDisjointObjectProperties e es
  <|> do
    s <- sameOrDifferentIndu
    as <- annotations
    is <- sepByComma individualUri
    return $ PlainAxiom as $ SameOrDifferentIndividual s is

frames :: CharParser st [Axiom]
frames = flat $ many $ classFrame
  <|> objectPropertyFrame <|> dataPropertyFrame <|> individualFrame
  <|> single misc

nsEntry :: CharParser st (String, QName)
nsEntry = do
    pkeyword prefixC
    p <- skips (option "" prefix << char ':')
    i <- skips fullIri
    return (p, i)
  <|> do
    pkeyword "Namespace:"
    p <- skips prefix
    i <- skips fullIri
    return (p, i)

importEntry :: CharParser st QName
importEntry = pkeyword importC >> uriP

basicSpec :: CharParser st OntologyFile
basicSpec = do
  nss <- many nsEntry
  option () $ pkeyword ontologyC >> uriP >> return ()
  many importEntry
  many realAnnotations
  as <- frames
  return emptyOntologyFile
    { ontology = emptyOntology
      { axiomsList = as
      , uri = dummyQName }
    , namespaces = Map.fromList $
      [ ("owl", "http://www.w3.org/2002/07/owl#")
      , ("rdf", "http://www.w3.org/1999/02/22-rdf-syntax-ns#")
      , ("rdfs", "http://www.w3.org/2000/01/rdf-schema#")
      , ("xsd", "http://www.w3.org/2001/XMLSchema#")
      , ("owl2xml", "http://www.w3.org/2006/12/owl2-xml#") ]
      ++ map (\ (p, q) -> (p, showQU q)) nss }
