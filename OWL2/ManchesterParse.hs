{- |
Module      :  $Header$
ClassExpression :  Manchester syntax parser for OWL 2
Copyright   :  (c) DFKI GmbH, Uni Bremen 2007-2010
License     :  GPLv2 or higher, see LICENSE.txt

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

module OWL2.ManchesterParse ({-basicSpec, symbItems, symbMapItems-}) where

import OWL2.AS
import OWL2.MS
import OWL.Keywords
import OWL.ColonKeywords

import Common.Keywords
import Common.Lexer
import Common.Parsec
import Common.AnnoParser (commentLine)
import Common.Token (criticalKeywords)
import Common.Utils (nubOrd)

import Text.ParserCombinators.Parsec
import Data.Char
import qualified Data.Map as Map

type URI = IRI

characters :: [Character]
characters = [minBound .. maxBound]

-- | OWL and CASL structured keywords including 'andS' and 'notS'
owlKeywords :: [String]
owlKeywords = notS : stringS : map show entityTypes
  ++ map show characters ++ keywords ++ criticalKeywords

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

{- comma and parens are removed here
   but would cause no problems for full IRIs within angle brackets -}
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

{- within abbreviated IRIs only ipath-noscheme should be used
   that excludes colons via isegment-nz-nc -}
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

uriP :: CharParser st QName
uriP =
  skips $ try $ checkWithUsing showQN uriQ $ \ q -> let p = namePrefix q in
  if null p then notElem (localPart q) owlKeywords
   else notElem p $ map (takeWhile (/= ':'))
        $ colonKeywords
        ++ [ show d ++ e | d <- equivOrDisjointL, e <- [classesC, propertiesC]]

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

withOrWithoutLanguage :: String -> Maybe String
withOrWithoutLanguage x = if x == "" then Nothing else Just x

stringLiteral :: CharParser st Literal
stringLiteral = do
  s <- stringLit
  do
      string cTypeS
      d <- datatypeUri
      return $ Literal s $ Typed d
    <|> do
      string asP
      t <- optionL $ skips languageTag
      return $ Literal s $ Untyped (withOrWithoutLanguage t)
    <|> skips (return $ Literal s $ Typed $ mkQName stringS)

literal :: CharParser st Literal
literal = do
    f <- skips $ try floatingPointLit
    return $ Literal f $ Typed $ mkQName floatS
  <|> do
    d <- skips decimalLit
    return $ Literal d $ Typed $ mkQName
      $ if any (== '.') d then decimalS else integerS
  <|> stringLiteral

-- * description

owlClassUri :: CharParser st QName
owlClassUri = uriP

individualUri :: CharParser st QName
individualUri = uriP

individual :: CharParser st Individual
individual = individualUri

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
atomic :: CharParser st ClassExpression
atomic = parensP description
  <|> fmap ObjectOneOf (bracesP $ sepByComma individual)

objectPropertyExpr :: CharParser st ObjectPropertyExpression
objectPropertyExpr = do
    keyword inverseS
    fmap ObjectInverseOf objectPropertyExpr
  <|> fmap ObjectProp uriP


-- creating the facet-value pairs
facetValuePair :: CharParser st (ConstrainingFacet, RestrictionValue)
facetValuePair = do
  df <- uriP
  rv <- literal
  return (df, rv)


-- it returns DataType Datatype or DatatypeRestriction Datatype [facetValuePair]
dataRangeRestriction :: CharParser st DataRange
dataRangeRestriction = do
  e <- datatypeUri
  option (DataType e) $ fmap (DatatypeRestriction e) $ bracketsP
    $ sepByComma facetValuePair

dataConjunct :: CharParser st DataRange
dataConjunct = fmap (mkDataJunction IntersectionOf) $ sepBy1 dataPrimary $ keyword andS

dataRange :: CharParser st DataRange
dataRange = fmap (mkDataJunction UnionOf) $ sepBy1 dataConjunct $ keyword orS

dataPrimary :: CharParser st DataRange
dataPrimary = do
    keyword notS
    fmap DataComplementOf dataPrimary
   <|> fmap DataOneOf (bracesP $ sepByComma literal)
   <|> dataRangeRestriction

mkDataJunction :: JunctionType -> [DataRange] -> DataRange
mkDataJunction ty ds = case nubOrd ds of
  [] -> error "mkObjectJunction"
  [x] -> x
  ns -> DataJunction ty ns

--the input must be "some" or "only" in order for the parsing to succeed
someOrOnly :: CharParser st QuantifierType
someOrOnly = choice
  $ map (\ f -> keyword (showQuantifierType f) >> return f)
    [AllValuesFrom, SomeValuesFrom]

-- locates the keywords "min" "max" "exact" and their argument
card :: CharParser st (CardinalityType, Int)
card = do
  c <- choice $ map (\ f -> keywordNotFollowedBy (showCardinalityType f) letter
                            >> return f)
             [MinCardinality, MaxCardinality, ExactCardinality]
  n <- skips getNumber
  return (c, value 10 n)

-- tries to parse either a QName or a literal
individualOrConstant :: CharParser st (Either Individual Literal)
individualOrConstant = fmap Right literal <|> fmap Left individual

-- applies the previous one to a list separated by commas (the list needs to be all of the same type, of course)
individualOrConstantList :: CharParser st (Either [Individual] [Literal])
individualOrConstantList = do
    ioc <- individualOrConstant
    case ioc of
      Left u -> fmap (Left . (u :)) $ optionL
        $ commaP >> sepByComma individual
      Right c -> fmap (Right . (c :)) $ optionL
        $ commaP >> sepByComma literal

primaryOrDataRange :: CharParser st (Either ClassExpression DataRange)
primaryOrDataRange = do
  ns <- many $ keyword notS  -- allows multiple not before primary
  ed <- do
      u <- datatypeUri
      fmap Left (restrictionAny $ ObjectProp u)
        <|> fmap (Right . DatatypeRestriction u)
            (bracketsP $ sepByComma facetValuePair)
        <|> return (if elem (localPart u) datatypeKeys
                       && elem (namePrefix u) ["", "xsd"]
              then Right $ DataType u
              else Left $ Expression u) -- could still be a datatypeUri
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

mkObjectJunction :: JunctionType -> [ClassExpression] -> ClassExpression
mkObjectJunction ty ds = case nubOrd ds of
  [] -> error "mkObjectJunction"
  [x] -> x
  ns -> ObjectJunction ty ns

restrictionAny :: ObjectPropertyExpression -> CharParser st ClassExpression
restrictionAny opExpr = do
      keyword valueS
      e <- individualOrConstant
      case e of
        Left u -> return $ ObjectHasValue opExpr u
        Right c -> case opExpr of
          ObjectProp dpExpr -> return $ DataHasValue dpExpr c
          _ -> unexpected "literal"
    <|> do
      keyword selfS
      return $ ObjectHasSelf opExpr
    <|> do -- sugar
      keyword onlysomeS
      ds <- bracketsP $ sepByComma description
      let as = map (ObjectValuesFrom SomeValuesFrom opExpr) ds
          o = ObjectValuesFrom AllValuesFrom opExpr
              $ mkObjectJunction UnionOf ds
      return $ mkObjectJunction IntersectionOf $ o : as
    <|> do -- sugar
      keyword hasS
      iu <- individual
      return $ ObjectValuesFrom SomeValuesFrom opExpr $ ObjectOneOf [iu]
    <|> do
      v <- someOrOnly
      pr <- primaryOrDataRange
      case pr of
        Left p -> return $ ObjectValuesFrom v opExpr p
        Right r -> case opExpr of
          ObjectProp dpExpr -> return $ DataValuesFrom v dpExpr [] r
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
             ObjectProp dpExpr ->
               return $ DataCardinality $ Cardinality c n dpExpr $ Just r
             _ -> unexpected $ "dataRange after " ++ showCardinalityType c

restriction :: CharParser st ClassExpression
restriction = objectPropertyExpr >>= restrictionAny

restrictionOrAtomic :: CharParser st ClassExpression
restrictionOrAtomic = do
    opExpr <- objectPropertyExpr
    restrictionAny opExpr <|> case opExpr of
       ObjectProp euri -> return $ Expression euri
       _ -> unexpected "inverse object property"
  <|> atomic

optNot :: (a -> a) -> CharParser st a -> CharParser st a
optNot f p = (keyword notS >> fmap f p) <|> p

primary :: CharParser st ClassExpression
primary = optNot ObjectComplementOf restrictionOrAtomic

conjunction :: CharParser st ClassExpression
conjunction = do
    curi <- fmap Expression $ try (owlClassUri << keyword thatS)
    rs <- sepBy1 (optNot ObjectComplementOf restriction) $ keyword andS
    return $ mkObjectJunction IntersectionOf $ curi : rs
  <|> fmap (mkObjectJunction IntersectionOf)
      (sepBy1 primary $ keyword andS)

description :: CharParser st ClassExpression
description =
  fmap (mkObjectJunction UnionOf) $ sepBy1 conjunction $ keyword orS


entityType :: CharParser st EntityType
entityType = choice $ map (\ f -> keyword (show f) >> return f)
  entityTypes

entity :: CharParser st Entity
entity = do
  t <- entityType
  u <- parensP uriP
  return $ Entity t u

-- same as annotation Target in Manchester Syntax, named annotation Value in Abstract Syntax
annotationValue :: CharParser st AnnotationValue
annotationValue = do
    i <- individual
    return $ AnnValue i
  <|> do
    l <- literal
    return $ AnnValLit l

annotation :: CharParser st Annotation
annotation = do
    ap <- uriP
    av <- annotationValue
    return $ Annotation [] ap av

optAnnos :: CharParser st a -> CharParser st ([Annotation], a)
optAnnos p = do
  as <- annotationList
  a <- p
  return (as, a)

optAnnos2 :: CharParser st Annotation
optAnnos2 = do
  as <- annotationList
  Annotation _ ap av <- annotation
  return $ Annotation as ap av

annotationList :: CharParser st [Annotation]
annotationList = optionL realAnnotations

realAnnotations :: CharParser st [Annotation]
realAnnotations = do
  pkeyword annotationsC
  sepByComma $ optAnnos2

descriptionAnnotatedList :: CharParser st [([Annotation], ClassExpression)]
descriptionAnnotatedList = sepByComma $ optAnnos description

annotationPropertyFrame :: CharParser st [AnnotationFrame]
annotationPropertyFrame = do
  pkeyword annotationPropertyC
  ap <- uriP
  x <- flat $ many $ apBit 
  return [AnnotationFrame ap x]


apBit :: CharParser st [AnnotationBit]
apBit = do
          pkeyword subPropertyOfC
          x <- sepByComma $ optAnnos uriP
          return [AnnotationSubPropertyOf $ AnnotatedList x] 
        <|> do
          pkeyword rangeC
          x <- sepByComma $ optAnnos uriP
          return [AnnotationDOR AnnRange $ AnnotatedList x ]
       <|> do
          pkeyword domainC
          x <- sepByComma $ optAnnos uriP
          return [AnnotationDOR AnnDomain $ AnnotatedList x ]
       <|> do
          pkeyword annotationsC
          x <- sepByComma $ optAnnos annotation
          return [AnnotationAnnotations $ AnnotatedList x] 


equivOrDisjointL :: [EquivOrDisjoint]
equivOrDisjointL = [Equivalent, Disjoint]

equivOrDisjoint :: CharParser st EquivOrDisjoint
equivOrDisjoint = choice
  $ map (\ f -> pkeyword (showEquivOrDisjoint f) >> return f)
  equivOrDisjointL

datatypeFrame :: CharParser st [Axiom]
datatypeFrame = do
    pkeyword datatypeC
    duri <- datatypeUri
    as1 <- many realAnnotations
    ms <- optionMaybe $ do
      pkeyword equivalentToC
      al <- annotationList
      dr <- dataRange
      return (al, dr)
    as2 <- many realAnnotations
    return $ map (\ an -> EntityAnno $ AnnotationAssertion an duri) as1
     ++ case ms of
      Nothing -> [ EntityAnno $ AnnotationAssertion (concat $ as1 ++ as2) duri ]
      Just (al, dr) -> [ PlainAxiom al $ DatatypeDefinition duri dr ]
     ++ map (\ an -> EntityAnno $ AnnotationAssertion an duri) as2

entityAnnos :: QName -> EntityType -> CharParser st [Axiom]
entityAnnos qn ty = do
    as <- realAnnotations
    return [PlainAxiom as $ Declaration $ Entity ty qn]

classFrame :: CharParser st [Axiom]
classFrame = do
        pkeyword classC
        iri <- uriP
        plain <- flat $ many $ classFrameBit iri
        if null plain then return [PlainAxiom [] $ Declaration $ Entity Class iri]
                      else return plain

classFrameBit :: QName -> CharParser st [Axiom]
classFrameBit curi = let duri = Expression curi in
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
    as <- annotationList
    ds <- sepByComma description
    return [PlainAxiom as $ DisjointUnion curi ds]
  <|> do
    pkeyword hasKeyC
    as <- annotationList
    o <- sepByComma objectPropertyExpr
    return [PlainAxiom as $ HasKey duri o []]

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
objectFrameBit ouri = let opExp = ObjectProp ouri in
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
    as <- annotationList
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
    as <- annotationList
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
      c <- literal
      return $ DataPropertyAssertion $ Assertion u pn iuri c
    <|> do
      t <- individualUri
      return $ ObjectPropertyAssertion $ Assertion (ObjectProp u) pn iuri t

iFrameBit :: QName -> CharParser st [Axiom]
iFrameBit iuri =
    entityAnnos iuri NamedIndividual
  <|> do
    pkeyword typesC
    ds <- descriptionAnnotatedList
    return $ map (\ (as, d) -> PlainAxiom as $ ClassAssertion d iuri) ds
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
equivOrDisjointKeyword ext = choice
  $ map (\ f -> pkeyword (show f ++ ext) >> return f)
  equivOrDisjointL

-- note the plural when different
sameOrDifferentIndu :: CharParser st SameOrDifferent
sameOrDifferentIndu =
  (pkeyword sameIndividualC >> return Same)
  <|> (pkeyword differentIndividualsC >> return Different)



misc :: CharParser st Axiom
misc = do
    e <- equivOrDisjointKeyword classesC
    as <- annotationList
    ds <- sepByComma description
    return $ PlainAxiom as $ EquivOrDisjointClasses e ds
  <|> do
    e <- equivOrDisjointKeyword propertiesC
    as <- annotationList
    es <- sepByComma objectPropertyExpr
    -- indistinguishable from dataProperties
    return $ PlainAxiom as $ EquivOrDisjointObjectProperties e es
  <|> do
    s <- sameOrDifferentIndu
    as <- annotationList
    is <- sepByComma individualUri
    return $ PlainAxiom as $ SameOrDifferentIndividual s is
{-
frames :: CharParser st [Axiom]
frames = flat $ many $ datatypeFrame <|> classFrame
  <|> objectPropertyFrame <|> dataPropertyFrame <|> individualFrame
  <|> annotationPropertyFrame <|> single misc

nsEntry :: CharParser st (String, QName)
nsEntry = do
    pkeyword prefixC
    p <- skips (option "" prefix << char ':')
    i <- skips fullIri
    return (p, i)
  <|> do
    pkeyword namespaceC
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
    , prefixName = Map.fromList $
      [ ("owl", "http://www.w3.org/2002/07/owl#")
      , ("rdf", "http://www.w3.org/1999/02/22-rdf-syntax-ns#")
      , ("rdfs", "http://www.w3.org/2000/01/rdf-schema#")
      , ("xsd", "http://www.w3.org/2001/XMLSchema#")
--      , ("", showQU dummyQName ++ "#") -- uncomment for API v3
      , ("owl2xml", "http://www.w3.org/2006/12/owl2-xml#") ]
      ++ map (\ (p, q) -> (p, showQU q)) nss }
-}
