{- |
Module      :  $Header$
Description :  Manchester syntax parser for OWL 2
Copyright   :  (c) DFKI GmbH, Uni Bremen 2007-2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Contains    :  Parser for the Manchester Syntax into Abstract Syntax of OWL 2

References  :  <http://www.w3.org/TR/2009/NOTE-owl2-manchester-syntax-20091027/>
-}

module OWL2.Parse where

import OWL2.AS
import OWL2.Symbols
import OWL2.Keywords
import OWL2.ColonKeywords

import Common.Keywords
import Common.Id
import Common.Lexer
import Common.Parsec
import Common.AnnoParser (commentLine)
import Common.Token (criticalKeywords)
import Common.Utils (nubOrd)
import qualified Common.IRI as IRI
import qualified Common.GlobalAnnotations as GA (PrefixMap)

import Text.ParserCombinators.Parsec
import Control.Monad (liftM2)
import Data.Char
import qualified Data.Map as Map

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
hierPartWithOpts = (char '#' <:> ifragment) <|> ihierPart <++> optQueryOrFrag

skips :: CharParser st a -> CharParser st a
skips = (<< skipMany
        (forget space <|> forget commentLine <|> nestCommentOut <?> ""))

abbrIriNoPos :: CharParser st QName
abbrIriNoPos = try $ do
    pre <- try $ prefix << char ':'
    r <- hierPartWithOpts <|> return "" -- allow an empty local part
    return nullQName { namePrefix = pre, localPart = r }
  <|> fmap mkQName hierPartWithOpts

abbrIri :: CharParser st QName
abbrIri = do
  p <- getPos
  q <- abbrIriNoPos
  return q { iriPos = Range [p],
                iriType = if namePrefix q == "_" then NodeID else Abbreviated }

fullIri :: CharParser st QName
fullIri = do
    char '<'
    QN pre r _ _ p <- abbrIri
    char '>'
    return $ QN pre r Full (if null pre then r else pre ++ ":" ++ r) p

uriQ :: CharParser st QName
uriQ = fullIri <|> abbrIri

uriP :: CharParser st QName
uriP =
  skips $ try $ checkWithUsing showQN uriQ $ \ q -> let p = namePrefix q in
  if null p then notElem (localPart q) owlKeywords
   else notElem p $ map (takeWhile (/= ':'))
        $ colonKeywords
        ++ [ show d ++ e | d <- equivOrDisjointL, e <- [classesC, propertiesC]]

extEntity :: CharParser st ExtEntityType
extEntity =
    fmap EntityType entityType
   <|> option AnyEntity (pkeyword "Prefix" >> return PrefixO)

symbItem :: GenParser Char st SymbItems
symbItem = do
    ext <- extEntity
    i <- uriP
    return $ SymbItems ext [i]

symbItems :: GenParser Char st SymbItems
symbItems = do
    ext <- extEntity
    iris <- symbs
    return $ SymbItems ext iris

-- | parse a comma separated list of uris
symbs :: GenParser Char st [IRI]
symbs = uriP >>= \ u -> do
    commaP `followedWith` uriP
    us <- symbs
    return $ u : us
  <|> return [u]

-- | parse a possibly kinded list of comma separated symbol pairs
symbMapItems :: GenParser Char st SymbMapItems
symbMapItems = do
  ext <- extEntity
  iris <- symbPairs
  return $ SymbMapItems ext iris

-- | parse a comma separated list of uri pairs
symbPairs :: GenParser Char st [(IRI, Maybe IRI)]
symbPairs = uriPair >>= \ u -> do
    commaP `followedWith` uriP
    us <- symbPairs
    return $ u : us
  <|> return [u]

uriPair :: GenParser Char st (IRI, Maybe IRI)
uriPair = uriP >>= \ u -> do
    pToken $ toKey mapsTo
    u2 <- uriP
    return (u, Just u2)
  <|> return (u, Nothing)

datatypeUri :: CharParser st QName
datatypeUri = fmap mkQName (choice $ map keyword datatypeKeys) <|> uriP

optSign :: CharParser st Bool
optSign = option False $ fmap (== '-') (oneOf "+-")

postDecimal :: CharParser st NNInt
postDecimal = char '.' >> option zeroNNInt getNNInt

getNNInt :: CharParser st NNInt
getNNInt = fmap (NNInt . map digitToInt) getNumber

intLit :: CharParser st IntLit
intLit = do
  b <- optSign
  n <- getNNInt
  return $ negNNInt b n

decimalLit :: CharParser st DecLit
decimalLit = liftM2 DecLit intLit $ option zeroNNInt postDecimal

floatDecimal :: CharParser st DecLit
floatDecimal = do
    n <- getNNInt
    f <- option zeroNNInt postDecimal
    return $ DecLit (negNNInt False n) f
   <|> do
    n <- postDecimal
    return $ DecLit zeroInt n

floatingPointLit :: CharParser st FloatLit
floatingPointLit = do
   b <- optSign
   d <- floatDecimal
   i <- option zeroInt (oneOf "eE" >> intLit)
   optionMaybe $ oneOf "fF"
   return $ FloatLit (negDec b d) i

languageTag :: CharParser st String
languageTag = atMost1 4 letter
  <++> flat (many $ char '-' <:> atMost1 8 alphaNum)

rmQuotes :: String -> String
rmQuotes s = case s of
  _ : tl@(_ : _) -> init tl
  _ -> error "rmQuotes"

stringLiteral :: CharParser st Literal
stringLiteral = do
  s <- fmap rmQuotes stringLit
  do
      string cTypeS
      d <- datatypeUri
      return $ Literal s $ Typed d
    <|> do
        string asP
        t <- skips $ optionMaybe languageTag
        return $ Literal s $ Untyped t
    <|> skips (return $ Literal s $ Typed $ mkQName stringS)

literal :: CharParser st Literal
literal = do
    f <- skips $ try floatingPointLit
         <|> fmap decToFloat decimalLit
    return $ NumberLit f
  <|> stringLiteral

-- * description

owlClassUri :: CharParser st QName
owlClassUri = uriP

individualUri :: CharParser st QName
individualUri = uriP

individual :: CharParser st Individual
individual = do
    i <- individualUri
    return $ if namePrefix i == "_" then i {iriType = NodeID}
                                    else i

skipChar :: Char -> CharParser st ()
skipChar = forget . skips . char

parensP :: CharParser st a -> CharParser st a
parensP = between (skipChar '(') (skipChar ')')

bracesP :: CharParser st a -> CharParser st a
bracesP = between (skipChar '{') (skipChar '}')

bracketsP :: CharParser st a -> CharParser st a
bracketsP = between (skipChar '[') (skipChar ']')

commaP :: CharParser st ()
commaP = forget $ skipChar ','

sepByComma :: CharParser st a -> CharParser st [a]
sepByComma p = sepBy1 p commaP

-- | plain string parser with skip
pkeyword :: String -> CharParser st ()
pkeyword s = forget . keywordNotFollowedBy s $ alphaNum <|> char '/'

keywordNotFollowedBy :: String -> CharParser st Char -> CharParser st String
keywordNotFollowedBy s c = skips $ try $ string s << notFollowedBy c

-- | keyword not followed by any alphanum
keyword :: String -> CharParser st String
keyword s = keywordNotFollowedBy s (alphaNum <|> char '_')

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
  rv <- literal
  return (facetToIRI df, rv)

-- it returns DataType Datatype or DatatypeRestriction Datatype [facetValuePair]
dataRangeRestriction :: CharParser st DataRange
dataRangeRestriction = do
  e <- datatypeUri
  option (DataType e []) $ fmap (DataType e) $ bracketsP
    $ sepByComma facetValuePair

dataConjunct :: CharParser st DataRange
dataConjunct = fmap (mkDataJunction IntersectionOf)
      $ sepBy1 dataPrimary $ keyword andS

dataRange :: CharParser st DataRange
dataRange = fmap (mkDataJunction UnionOf)
      $ sepBy1 dataConjunct $ keyword orS

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

-- parses "some" or "only"
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

{- | applies the previous one to a list separated by commas
    (the list needs to be all of the same type, of course) -}
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
        <|> fmap (Right . DataType u)
            (bracketsP $ sepByComma facetValuePair)
        <|> return (if isDatatypeKey u
              then Right $ DataType u []
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
          ObjectProp dpExpr -> return $ DataValuesFrom v dpExpr r
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

{- | same as annotation Target in Manchester Syntax,
      named annotation Value in Abstract Syntax -}
annotationValue :: CharParser st AnnotationValue
annotationValue = do
    l <- literal
    return $ AnnValLit l
  <|> do
    i <- individual
    return $ AnnValue i

equivOrDisjointL :: [EquivOrDisjoint]
equivOrDisjointL = [Equivalent, Disjoint]

equivOrDisjoint :: CharParser st EquivOrDisjoint
equivOrDisjoint = choice
  $ map (\ f -> pkeyword (showEquivOrDisjoint f) >> return f)
  equivOrDisjointL

subPropertyKey :: CharParser st ()
subPropertyKey = pkeyword subPropertyOfC

characterKey :: CharParser st ()
characterKey = pkeyword characteristicsC

sameOrDifferent :: CharParser st SameOrDifferent
sameOrDifferent = choice
  $ map (\ f -> pkeyword (showSameOrDifferent f) >> return f)
  [Same, Different]

sameOrDifferentIndu :: CharParser st SameOrDifferent
sameOrDifferentIndu = (pkeyword sameIndividualC >> return Same)
    <|> (pkeyword differentIndividualsC >> return Different)

equivOrDisjointKeyword :: String -> CharParser st EquivOrDisjoint
equivOrDisjointKeyword ext = choice
  $ map (\ f -> pkeyword (show f ++ ext) >> return f)
  equivOrDisjointL

objectPropertyCharacter :: CharParser st Character
objectPropertyCharacter =
  choice $ map (\ f -> keyword (show f) >> return f) characters

domainOrRange :: CharParser st DomainOrRange
domainOrRange = choice
  $ map (\ f -> pkeyword (showDomainOrRange f) >> return f)
  [ADomain, ARange]

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

convertPrefixMap :: GA.PrefixMap -> Map.Map String String
convertPrefixMap = Map.map $ IRI.iriToStringUnsecure . IRI.setAngles False
