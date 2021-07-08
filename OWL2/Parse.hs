{- |
Module      :  ./OWL2/Parse.hs
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

import qualified OWL2.AS as AS
import OWL2.Symbols
import OWL2.Keywords
import OWL2.ColonKeywords

import Common.Keywords
import Common.Id
import Common.IRI
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

characters :: [AS.Character]
characters = [minBound .. maxBound]

-- | OWL and CASL structured keywords including 'andS' and 'notS'
owlKeywords :: [String]
owlKeywords = notS : stringS : map show AS.entityTypes
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


uriQ :: CharParser st IRI
-- uriQ = fullIri <|> abbrIri
uriQ = Common.IRI.compoundIriCurie

fullIri :: CharParser st IRI
fullIri = angles iriParser

uriP :: CharParser st IRI
uriP =
  skips $ try $ checkWithUsing showIRI uriQ $ \ q -> let p = prefixName q in
  if null p then notElem (show $ iriPath q) owlKeywords
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

datatypeUri :: CharParser st IRI
datatypeUri = fmap mkIRI (choice $ map keyword datatypeKeys) <|> uriP

optSign :: CharParser st Bool
optSign = option False $ fmap (== '-') (oneOf "+-")

postDecimal :: CharParser st AS.NNInt
postDecimal = char '.' >> option AS.zeroNNInt getNNInt

getNNInt :: CharParser st AS.NNInt
getNNInt = fmap (AS.NNInt . map digitToInt) getNumber

intLit :: CharParser st AS.IntLit
intLit = do
  b <- optSign
  n <- getNNInt
  return $ AS.negNNInt b n

decimalLit :: CharParser st AS.DecLit
decimalLit = liftM2 AS.DecLit intLit $ option AS.zeroNNInt postDecimal

floatDecimal :: CharParser st AS.DecLit
floatDecimal = do
    n <- getNNInt
    f <- option AS.zeroNNInt postDecimal
    return $ AS.DecLit (AS.negNNInt False n) f
   <|> do
    n <- postDecimal
    return $ AS.DecLit AS.zeroInt n

floatingPointLit :: CharParser st AS.FloatLit
floatingPointLit = do
   b <- optSign
   d <- floatDecimal
   i <- option AS.zeroInt (oneOf "eE" >> intLit)
   optionMaybe $ oneOf "fF"
   return $ AS.FloatLit (AS.negDec b d) i

languageTag :: CharParser st String
languageTag = atMost1 4 letter
  <++> flat (many $ char '-' <:> atMost1 8 alphaNum)

rmQuotes :: String -> String
rmQuotes s = case s of
  _ : tl@(_ : _) -> init tl
  _ -> error "rmQuotes"

stringLiteral :: CharParser st AS.Literal
stringLiteral = do
  s <- fmap rmQuotes stringLit
  do
      string AS.cTypeS
      d <- datatypeUri
      return $ AS.Literal s $ AS.Typed d
    <|> do
        string asP
        t <- skips $ optionMaybe languageTag
        return $ AS.Literal s $ AS.Untyped t
    <|> skips (return $ AS.Literal s $ AS.Typed $ mkIRI stringS) {prefixName = "xsd"} )

literal :: CharParser st AS.Literal
literal = do
    f <- skips $ try floatingPointLit
         <|> fmap AS.decToFloat decimalLit
    return $ AS.NumberLit f
  <|> stringLiteral

-- * description

owlClassUri :: CharParser st IRI
owlClassUri = uriP

individualUri :: CharParser st IRI
individualUri = uriP

individual :: CharParser st AS.Individual
individual = do
    i <- individualUri
    return $ if prefixName i == "_" then i {isBlankNode = True}
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
atomic :: CharParser st AS.ClassExpression
atomic = parensP description
  <|> fmap AS.ObjectOneOf (bracesP $ sepByComma individual)

objectPropertyExpr :: CharParser st AS.ObjectPropertyExpression
objectPropertyExpr = do
    keyword inverseS
    fmap AS.ObjectInverseOf objectPropertyExpr
  <|> fmap AS.ObjectProp uriP

-- creating the facet-value pairs
facetValuePair :: CharParser st (AS.ConstrainingFacet, AS.RestrictionValue)
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
  return (AS.facetToIRI df, rv)

-- it returns DataType Datatype or DatatypeRestriction Datatype [facetValuePair]
dataRangeRestriction :: CharParser st AS.DataRange
dataRangeRestriction = do
  e <- datatypeUri
  option (AS.DataType e []) $ fmap (AS.DataType e) $ bracketsP
    $ sepByComma facetValuePair

dataConjunct :: CharParser st AS.DataRange
dataConjunct = fmap (mkDataJunction AS.IntersectionOf)
      $ sepBy1 dataPrimary $ keyword andS

dataRange :: CharParser st AS.DataRange
dataRange = fmap (mkDataJunction AS.UnionOf)
      $ sepBy1 dataConjunct $ keyword orS

dataPrimary :: CharParser st AS.DataRange
dataPrimary = do
    keyword notS
    fmap AS.DataComplementOf dataPrimary
   <|> fmap AS.DataOneOf (bracesP $ sepByComma literal)
   <|> dataRangeRestriction

mkDataJunction :: AS.JunctionType -> [AS.DataRange] -> AS.DataRange
mkDataJunction ty ds = case nubOrd ds of
  [] -> error "mkDataJunction"
  [x] -> x
  ns -> AS.DataJunction ty ns

-- parses "some" or "only"
someOrOnly :: CharParser st AS.QuantifierType
someOrOnly = choice
  $ map (\ f -> keyword (AS.showQuantifierType f) >> return f)
    [AS.AllValuesFrom, AS.SomeValuesFrom]

-- locates the keywords "min" "max" "exact" and their argument
card :: CharParser st (AS.CardinalityType, Int)
card = do
  c <- choice $ map (\ f -> keywordNotFollowedBy (AS.showCardinalityType f) letter
                            >> return f)
             [AS.MinCardinality, AS.MaxCardinality, AS.ExactCardinality]
  n <- skips getNumber
  return (c, value 10 n)

-- tries to parse either a IRI or a literal
individualOrConstant :: CharParser st (Either AS.Individual AS.Literal)
individualOrConstant = fmap Right literal <|> fmap Left individual

{- | applies the previous one to a list separated by commas
    (the list needs to be all of the same type, of course) -}
individualOrConstantList :: CharParser st (Either [AS.Individual] [AS.Literal])
individualOrConstantList = do
    ioc <- individualOrConstant
    case ioc of
      Left u -> fmap (Left . (u :)) $ optionL
        $ commaP >> sepByComma individual
      Right c -> fmap (Right . (c :)) $ optionL
        $ commaP >> sepByComma literal

primaryOrDataRange :: CharParser st (Either AS.ClassExpression AS.DataRange)
primaryOrDataRange = do
  ns <- many $ keyword notS  -- allows multiple not before primary
  ed <- do
      u <- datatypeUri
      fmap Left (restrictionAny $ AS.ObjectProp u)
        <|> fmap (Right . AS.DataType u)
            (bracketsP $ sepByComma facetValuePair)
        <|> return (if AS.isDatatypeKey u
              then Right $ AS.DataType u []
              else Left $ AS.Expression u) -- could still be a datatypeUri
    <|> do
      e <- bracesP individualOrConstantList
      return $ case e of
        Left us -> Left $ AS.ObjectOneOf us
        Right cs -> Right $ AS.DataOneOf cs
    <|> fmap Left restrictionOrAtomic
  return $ if even (length ns) then ed else
    case ed of
      Left d -> Left $ AS.ObjectComplementOf d
      Right d -> Right $ AS.DataComplementOf d

mkObjectJunction :: AS.JunctionType -> [AS.ClassExpression] -> AS.ClassExpression
mkObjectJunction ty ds = case nubOrd ds of
  [] -> error "mkObjectJunction"
  [x] -> x
  ns -> AS.ObjectJunction ty ns

restrictionAny :: AS.ObjectPropertyExpression -> CharParser st AS.ClassExpression
restrictionAny opExpr = do
      keyword valueS
      e <- individualOrConstant
      case e of
        Left u -> return $ AS.ObjectHasValue opExpr u
        Right c -> case opExpr of
          AS.ObjectProp dpExpr -> return $ AS.DataHasValue dpExpr c
          _ -> unexpected "literal"
    <|> do
      keyword selfS
      return $ AS.ObjectHasSelf opExpr
    <|> do -- sugar
      keyword onlysomeS
      ds <- bracketsP $ sepByComma description
      let as = map (AS.ObjectValuesFrom AS.SomeValuesFrom opExpr) ds
          o = AS.ObjectValuesFrom AS.AllValuesFrom opExpr
              $ mkObjectJunction AS.UnionOf ds
      return $ mkObjectJunction AS.IntersectionOf $ o : as
    <|> do -- sugar
      keyword hasS
      iu <- individual
      return $ AS.ObjectValuesFrom AS.SomeValuesFrom opExpr $ AS.ObjectOneOf [iu]
    <|> do
      v <- someOrOnly
      pr <- primaryOrDataRange
      case pr of
        Left p -> return $ AS.ObjectValuesFrom v opExpr p
        Right r -> case opExpr of
          AS.ObjectProp dpExpr -> return $ AS.DataValuesFrom v [dpExpr] r
          _ -> unexpected $ "dataRange after " ++ AS.showQuantifierType v
    <|> do
      (c, n) <- card
      mp <- optionMaybe primaryOrDataRange
      case mp of
         Nothing -> return $ AS.ObjectCardinality $ AS.Cardinality c n opExpr Nothing
         Just pr -> case pr of
           Left p ->
             return $ AS.ObjectCardinality $ AS.Cardinality c n opExpr $ Just p
           Right r -> case opExpr of
             AS.ObjectProp dpExpr ->
               return $ AS.DataCardinality $ AS.Cardinality c n dpExpr $ Just r
             _ -> unexpected $ "dataRange after " ++ AS.showCardinalityType c

restriction :: CharParser st AS.ClassExpression
restriction = objectPropertyExpr >>= restrictionAny

restrictionOrAtomic :: CharParser st AS.ClassExpression
restrictionOrAtomic = do
    opExpr <- objectPropertyExpr
    restrictionAny opExpr <|> case opExpr of
       AS.ObjectProp euri -> return $ AS.Expression euri
       _ -> unexpected "inverse object property"
  <|> atomic

optNot :: (a -> a) -> CharParser st a -> CharParser st a
optNot f p = (keyword notS >> fmap f p) <|> p

primary :: CharParser st AS.ClassExpression
primary = optNot AS.ObjectComplementOf restrictionOrAtomic

conjunction :: CharParser st AS.ClassExpression
conjunction = do
    curi <- fmap AS.Expression $ try (owlClassUri << keyword thatS)
    rs <- sepBy1 (optNot AS.ObjectComplementOf restriction) $ keyword andS
    return $ mkObjectJunction AS.IntersectionOf $ curi : rs
  <|> fmap (mkObjectJunction AS.IntersectionOf)
      (sepBy1 primary $ keyword andS)

description :: CharParser st AS.ClassExpression
description =
  fmap (mkObjectJunction AS.UnionOf) $ sepBy1 conjunction $ keyword orS

entityType :: CharParser st AS.EntityType
entityType = choice $ map (\ f -> keyword (show f) >> return f)
  AS.entityTypes

{- | same as annotation Target in Manchester Syntax,
      named annotation Value in Abstract Syntax -}
annotationValue :: CharParser st AS.AnnotationValue
annotationValue = do
    l <- literal
    return $ AS.AnnValLit l
  <|> do
    i <- individual
    return $ AS.AnnValue i

equivOrDisjointL :: [AS.EquivOrDisjoint]
equivOrDisjointL = [AS.Equivalent, AS.Disjoint]

equivOrDisjoint :: CharParser st AS.EquivOrDisjoint
equivOrDisjoint = choice
  $ map (\ f -> pkeyword (AS.showEquivOrDisjoint f) >> return f)
  equivOrDisjointL

subPropertyKey :: CharParser st ()
subPropertyKey = pkeyword subPropertyOfC

characterKey :: CharParser st ()
characterKey = pkeyword characteristicsC

sameOrDifferent :: CharParser st AS.SameOrDifferent
sameOrDifferent = choice
  $ map (\ f -> pkeyword (AS.showSameOrDifferent f) >> return f)
  [AS.Same, AS.Different]

sameOrDifferentIndu :: CharParser st AS.SameOrDifferent
sameOrDifferentIndu = (pkeyword sameIndividualC >> return AS.Same)
    <|> (pkeyword differentIndividualsC >> return AS.Different)

equivOrDisjointKeyword :: String -> CharParser st AS.EquivOrDisjoint
equivOrDisjointKeyword ext = choice
  $ map (\ f -> pkeyword (show f ++ ext) >> return f)
  equivOrDisjointL

objectPropertyCharacter :: CharParser st AS.Character
objectPropertyCharacter =
  choice $ map (\ f -> keyword (show f) >> return f) characters

domainOrRange :: CharParser st AS.DomainOrRange
domainOrRange = choice
  $ map (\ f -> pkeyword (AS.showDomainOrRange f) >> return f)
  [AS.ADomain, AS.ARange]

nsEntry :: CharParser st (String, IRI)
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

importEntry :: CharParser st IRI
importEntry = pkeyword importC >> uriP

convertPrefixMap :: GA.PrefixMap -> Map.Map String String
convertPrefixMap = Map.map $ IRI.iriToStringUnsecure . IRI.setAngles False
