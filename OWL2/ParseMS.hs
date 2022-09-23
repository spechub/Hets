
{- |
Module      :  ./OWL2/ParseMS.hs
Copyright   :  (c) Björn Gehrke
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  bjoern.gehrke@ovgu.de
Stability   :  provisional
Portability :  portable
Manchester Syntax parser
References  :  <https://www.w3.org/TR/owl2-manchester-syntax/>
-}

module OWL2.ParseMS where

import Prelude hiding (lookup)

import OWL2.AS
import OWL2.Keywords hiding (comment)
import OWL2.ColonKeywords

import Common.Keywords
import Common.IRI
import Common.Id (stringToId)
import Common.Lexer
import Common.Parsec
import Common.AnnoParser (newlineOrEof, commentLine)
import Common.Token (criticalKeywords)
import Common.Utils (nubOrd)

import qualified Common.GlobalAnnotations as GA (PrefixMap)

import Text.ParserCombinators.Parsec

import Data.Char
import Data.Maybe (isJust)
import qualified Data.Map as Map (fromList, unions)
import Data.Either (partitionEithers)
import Control.Monad (liftM2, unless)
import qualified Control.Monad.Fail as Fail

type Annotations = [Annotation]
-- | Parses a comment
comment :: CharParser st ()
comment = try $ do
    char '#'
    manyTill anyChar newlineOrEof
    return ()

-- | Skips whitespaces and comments
skips :: CharParser st a -> CharParser st a
skips = (<< skipMany (forget space <|> comment <|> forget commentLine <|> forget nestCommentOut <?> "comment"))


skipChar :: Char -> CharParser st ()
skipChar = forget . skips . char


characters :: [Character]
characters = [minBound .. maxBound]

-- | OWL and CASL structured keywords including 'andS' and 'notS'
owlKeywords :: [String]
owlKeywords = endS : notS : stringS : map show entityTypes
  ++ map show characters ++ keywords ++ criticalKeywords

ncNameStart :: Char -> Bool
ncNameStart c = isAlpha c || c == '_'

-- | rfc3987 plus '+' from scheme (scheme does not allow the dots)
ncNameChar :: Char -> Bool
ncNameChar c = isAlphaNum c || elem c ".+-_\183"

prefix :: CharParser st String
prefix = satisfy ncNameStart <:> many (satisfy ncNameChar)


-- | parse zero or at most n consecutive arguments
atMost :: Int -> GenParser tok st a -> GenParser tok st [a]
atMost n p = if n <= 0 then return [] else
     p <:> atMost (n - 1) p <|> return []

-- | parse at least one but at most n conse
atMost1 :: Int -> GenParser tok st a -> GenParser tok st [a]
atMost1 n p = p <:> atMost (n - 1) p




uriQ :: CharParser st IRI
-- uriQ = fullIri <|> abbrIri
uriQ = iriCurie

fullIri :: CharParser st IRI
fullIri = angles iriParser

expUriP :: GA.PrefixMap -> CharParser st IRI
expUriP pm = uriP >>= return . expandIRI pm

uriP :: CharParser st IRI
uriP = skips $ try $ do
  colonM <- optionMaybe . try . lookAhead $ char ':'
  checkWithUsing (\i -> "keyword \"" ++ showIRI i ++ "\"") uriQ $ \ q -> let p = prefixName q in
    if not (isAbbrev q) || isJust colonM then True
    else if null p then notElem (iFragment q) owlKeywords
    else notElem p $ map (takeWhile (/= ':'))
        $ colonKeywords
        ++ [ show d ++ e | d <- equivOrDisjointL, e <- [classesC, propertiesC]]


datatypeKey :: GA.PrefixMap -> CharParser st IRI
datatypeKey pm = mkIRI <$> (choice $ map (try . keyword) datatypeKeys) >>=
    return . expandIRI pm . setPrefix "xsd"
  
dataPropertyExpr :: GA.PrefixMap -> CharParser st DataPropertyExpression
dataPropertyExpr = expUriP

datatypeUri :: GA.PrefixMap -> CharParser st IRI
datatypeUri pm = datatypeKey pm <|> expUriP pm

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

booleanLit :: GA.PrefixMap -> CharParser st Literal
booleanLit pm = do
  val <- skips $ try $ choice [string trueS, string falseS]
  let typed = Typed (expandIRI pm $ nullIRI { iriPath = stringToId booleanS,  iFragment = booleanS, isAbbrev = True, prefixName = "xsd"})
  return $ Literal val typed

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

charOrEscaped :: CharParser st Char
charOrEscaped = do
    c <- anyChar
    if c == '\\' then char '\\' <|> char '"' else return c

stringLiteral :: GA.PrefixMap -> CharParser st Literal
stringLiteral pm = do
  s <- char '"' >> manyTill charOrEscaped (char '"')
  do
      string cTypeS
      d <- datatypeUri pm
      return $ Literal s $ Typed d
    <|> do
        t <- skips $ optionMaybe (string asP >> languageTag)
        return $ Literal s $ Untyped t

literal :: GA.PrefixMap -> CharParser st Literal
literal pm = do
    f <- skips $ try floatingPointLit
         <|> fmap decToFloat decimalLit
    return $ NumberLit f
  <|> skips (stringLiteral pm)
  <|> booleanLit pm
  <?> "Literal"
-- * description

owlClassUri :: GA.PrefixMap -> CharParser st IRI
owlClassUri = expUriP

individualUri :: GA.PrefixMap -> CharParser st IRI
individualUri = expUriP

individual :: GA.PrefixMap -> CharParser st Individual
individual pm = do
    i <- individualUri pm
    return $ if prefixName i == "_" then i {isBlankNode = True}
                                    else i


parensP :: CharParser st a -> CharParser st a
parensP = between (skipChar '(') (skipChar ')')

optParensP :: CharParser st a -> CharParser st a
optParensP p = parensP p <|> p

bracesP :: CharParser st a -> CharParser st a
bracesP = between (skipChar '{') (skipChar '}')

bracketsP :: CharParser st a -> CharParser st a
bracketsP = between (skipChar '[') (skipChar ']')

commaP :: CharParser st ()
commaP = skipChar ','

sepByComma :: CharParser st a -> CharParser st [a]
sepByComma p = sepBy1 p $ try commaP

-- | plain string parser with skip
pkeyword :: String -> CharParser st ()
pkeyword s = forget $ keywordNotFollowedBy s (alphaNum <|> char '/')

keywordNotFollowedBy :: String -> CharParser st Char -> CharParser st String
keywordNotFollowedBy s c = skips $ try $ string s << notFollowedBy c

-- | keyword not followed by any alphanum
keyword :: String -> CharParser st String
keyword s = keywordNotFollowedBy s (alphaNum <|> char '_')

-- base OWLClass excluded
atomic :: GA.PrefixMap -> CharParser st ClassExpression
atomic pm = (parensP $ description pm)
  <|> ObjectOneOf <$> (bracesP $ sepByComma $ individual pm)

objectPropertyExpr :: GA.PrefixMap -> CharParser st ObjectPropertyExpression
objectPropertyExpr pm = 
  -- parenthesis around objectPropertyExpressions aren't defined in the standard but used by the Java OWL API
  do
    pkeyword inverseS
    ObjectInverseOf <$> optParensP (objectPropertyExpr pm)
  <|> ObjectProp <$> (expUriP pm)

parseProperties :: GA.PrefixMap -> CharParser st ([ObjectPropertyExpression], [DataPropertyExpression])
parseProperties pm = do
  props <- sepByComma $ choice [objectPropertyExpr pm >>= return . Left, expUriP pm >>= return . Right]
  return $ partitionEithers props


-- creating the facet-value pairs
facetValuePair :: GA.PrefixMap -> CharParser st (ConstrainingFacet, RestrictionValue)
facetValuePair pm = do
  df <- choice $ map (\ f -> pkeyword (showFacet f) >> return f)
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
  rv <- literal pm
  return (expandIRI pm (facetToIRINoSign df), rv)

-- it returns DataType Datatype or DatatypeRestriction Datatype [facetValuePair]
dataRangeRestriction :: GA.PrefixMap -> CharParser st DataRange
dataRangeRestriction pm = do
  e <- datatypeUri pm
  option (DataType e []) $ fmap (DataType e) $ try $ parseFacetValuePairs pm
    
parseFacetValuePairs :: GA.PrefixMap -> CharParser st [(ConstrainingFacet, RestrictionValue)]
parseFacetValuePairs pm = bracketsP $ sepByComma $ skips $ facetValuePair pm

dataConjunct :: GA.PrefixMap -> CharParser st DataRange
dataConjunct pm = fmap (mkDataJunction IntersectionOf)
      $ sepBy1 (dataPrimary pm) $ pkeyword andS

dataRange :: GA.PrefixMap -> CharParser st DataRange
dataRange pm = fmap (mkDataJunction UnionOf)
      $ sepBy1 (dataConjunct pm) $ pkeyword orS

dataPrimary :: GA.PrefixMap -> CharParser st DataRange
dataPrimary pm = do
    pkeyword notS
    fmap DataComplementOf (dataPrimary pm)
   <|> parensP (dataRange pm)
   <|> fmap DataOneOf (bracesP $ sepByComma $ literal pm)
   <|> dataRangeRestriction pm

mkDataJunction :: JunctionType -> [DataRange] -> DataRange
mkDataJunction ty ds = case nubOrd ds of
  [] -> error "mkDataJunction"
  [x] -> x
  ns -> DataJunction ty ns

-- parses "some" or "only"
someOrOnly :: CharParser st QuantifierType
someOrOnly = choice
  $ map (\ f -> pkeyword (showQuantifierType f) >> return f)
    [AllValuesFrom, SomeValuesFrom]

-- locates the keywords "min" "max" "exact" and their argument
card :: CharParser st (CardinalityType, Int)
card = do
  c <- choice $ map (\ f -> keywordNotFollowedBy (showCardinalityType f) letter
                            >> return f)
             [MinCardinality, MaxCardinality, ExactCardinality]
  n <- skips getNumber
  return (c, value 10 n)

-- tries to parse either a IRI or a literal
individualOrConstant :: GA.PrefixMap -> CharParser st (Either Individual Literal)
individualOrConstant pm = fmap Right (literal pm) <|> fmap Left (individual pm)

{- | applies the previous one to a list separated by commas
    (the list needs to be all of the same type, of course) -}
individualOrConstantList :: GA.PrefixMap -> CharParser st (Either [Individual] [Literal])
individualOrConstantList pm = do
    ioc <- individualOrConstant pm
    case ioc of
      Left u -> fmap (Left . (u :)) $ optionL
        $ commaP >> sepByComma (individual pm)
      Right c -> fmap (Right . (c :)) $ optionL
        $ commaP >> sepByComma (literal pm)

primaryOrDataRange :: GA.PrefixMap -> CharParser st (Either ClassExpression DataRange)
primaryOrDataRange pm = do
  ns <- many $ pkeyword notS  -- allows multiple not before primary
  ed <- do
      u <- datatypeUri pm
      fmap Left (restrictionAny pm $ ObjectProp u)
        <|> fmap (Right . DataType u)
            (bracketsP $ sepByComma $ facetValuePair pm)
        <|> return (if isDatatypeKey u
              then Right $ DataType u []
              else Left $ Expression u) -- could still be a datatypeUri
    <|> do
      e <- bracesP $ individualOrConstantList pm
      return $ case e of
        Left us -> Left $ ObjectOneOf us
        Right cs -> Right $ DataOneOf cs
    <|> fmap Left (restrictionOrAtomic pm)
  return $ if even (length ns) then ed else
    case ed of
      Left d -> Left $ ObjectComplementOf d
      Right d -> Right $ DataComplementOf d

mkObjectJunction :: JunctionType -> [ClassExpression] -> ClassExpression
mkObjectJunction ty ds = case nubOrd ds of
  [] -> error "mkObjectJunction"
  [x] -> x
  ns -> ObjectJunction ty ns

dataValuesFrom :: GA.PrefixMap -> CharParser st ClassExpression
dataValuesFrom pm = try $ do
    dpExprs <- parensP $ do
      dpExpr <- dataPropertyExpr pm
      commaP
      dpExprs <- sepByComma (dataPropertyExpr pm)
      return (dpExpr : dpExprs)
    s <- someOrOnly
    dp <- dataPrimary pm
    return $ DataValuesFrom s dpExprs dp

restrictionAny :: GA.PrefixMap -> ObjectPropertyExpression -> CharParser st ClassExpression
restrictionAny pm opExpr = do
      pkeyword valueS
      e <- individualOrConstant pm
      case e of
        Left u -> return $ ObjectHasValue opExpr u
        Right c -> case opExpr of
          ObjectProp dpExpr -> return $ DataHasValue dpExpr c
          _ -> unexpected "literal"
    <|> do
      pkeyword selfS
      return $ ObjectHasSelf opExpr
    <|> do -- sugar
      pkeyword onlysomeS
      ds <- bracketsP $ sepByComma $ description pm
      let as = map (ObjectValuesFrom SomeValuesFrom opExpr) ds
          o = ObjectValuesFrom AllValuesFrom opExpr
              $ mkObjectJunction UnionOf ds
      return $ mkObjectJunction IntersectionOf $ o : as
    <|> do -- sugar
      pkeyword hasS
      iu <- individual pm
      return $ ObjectValuesFrom SomeValuesFrom opExpr $ ObjectOneOf [iu]
    <|> do
      v <- someOrOnly
      pr <- primaryOrDataRange pm
      case pr of
        Left p -> return $ ObjectValuesFrom v opExpr p
        Right r -> case opExpr of
          ObjectProp dpExpr -> return $ DataValuesFrom v [dpExpr] r
          _ -> unexpected $ "dataRange after " ++ showQuantifierType v
    <|> do
      (c, n) <- card
      mp <- optionMaybe $ primaryOrDataRange pm
      case mp of
         Nothing -> return $ ObjectCardinality $ Cardinality c n opExpr Nothing
         Just pr -> case pr of
           Left p ->
             return $ ObjectCardinality $ Cardinality c n opExpr $ Just p
           Right r -> case opExpr of
             ObjectProp dpExpr ->
               return $ DataCardinality $ Cardinality c n dpExpr $ Just r
             _ -> unexpected $ "dataRange after " ++ showCardinalityType c

restriction :: GA.PrefixMap -> CharParser st ClassExpression
restriction pm = dataValuesFrom pm <|> (objectPropertyExpr pm >>= restrictionAny pm)

restrictionOrAtomic :: GA.PrefixMap -> CharParser st ClassExpression
restrictionOrAtomic pm = dataValuesFrom pm <|> do
    opExpr <- objectPropertyExpr pm
    restrictionAny pm opExpr <|> case opExpr of
       ObjectProp euri -> return $ Expression euri
       _ -> unexpected "inverse object property"
  <|> atomic pm

optNot :: (a -> a) -> CharParser st a -> CharParser st a
optNot f p = (pkeyword notS >> fmap f p) <|> p

primary :: GA.PrefixMap -> CharParser st ClassExpression
primary pm = optNot ObjectComplementOf (restrictionOrAtomic pm)

conjunction :: GA.PrefixMap -> CharParser st ClassExpression
conjunction pm = do
    curi <- Expression <$> try (owlClassUri pm << pkeyword thatS)
    rs <- sepBy1 (optNot ObjectComplementOf $ restriction pm) $ pkeyword andS
    return $ mkObjectJunction IntersectionOf $ curi : rs
  <|> (mkObjectJunction IntersectionOf) <$>
      (sepBy1 (skips $ primary pm) (pkeyword andS))

description :: GA.PrefixMap -> CharParser st ClassExpression
description pm =
  (mkObjectJunction UnionOf <$> sepBy1 (conjunction pm) (pkeyword orS))

{- | same as annotation Target in Manchester Syntax,
      named annotation Value in Abstract Syntax -}
annotationValue :: GA.PrefixMap -> CharParser st AnnotationValue
annotationValue pm = do
    l <- literal pm
    return $ AnnValLit l
  <|> do
    i <- individual pm
    return $ AnnValue i

equivOrDisjointL :: [EquivOrDisjoint]
equivOrDisjointL = [Equivalent, Disjoint]
objectPropertyCharacter :: 
  GA.PrefixMap ->
  ObjectPropertyExpression ->
  CharParser st ObjectPropertyAxiom
objectPropertyCharacter pm oe = do
  ans <- (optionalAnnos pm)
  ctor <- ((pkeyword functionalS >> return FunctionalObjectProperty) <|>
    (pkeyword inverseFunctionalS >> return InverseFunctionalObjectProperty) <|>
    (pkeyword reflexiveS >> return ReflexiveObjectProperty) <|>
    (pkeyword irreflexiveS >> return IrreflexiveObjectProperty) <|>
    (pkeyword symmetricS >> return SymmetricObjectProperty) <|>
    (pkeyword asymmetricS >> return AsymmetricObjectProperty) <|>
    (pkeyword transitiveS >> return TransitiveObjectProperty))
  return $ ctor ans oe


optAnnos :: GA.PrefixMap -> CharParser st a -> CharParser st (Annotations, a)
optAnnos pm p = do
    as <- optionalAnnos pm
    a <- p
    return (as, a)

optionalAnnos :: GA.PrefixMap -> CharParser st Annotations
optionalAnnos pm = option [] $ try $ annotations pm

annotations :: GA.PrefixMap -> CharParser st Annotations
annotations pm = do
    pkeyword annotationsC
    as <- sepByComma $ optAnnos pm $ try $ pair (expUriP pm) (skips $ annotationValue pm)
    return $ map (\(anns, (source, target)) -> Annotation anns source target) as

descriptionAnnotatedList :: GA.PrefixMap -> CharParser st [(Annotations, ClassExpression)]
descriptionAnnotatedList pm = sepByComma $ optAnnos pm (description pm)

annotationPropertyFrame :: GA.PrefixMap -> CharParser st [Axiom]
annotationPropertyFrame pm = do
    pkeyword annotationPropertyC
    annos <- optionalAnnos pm
    ap <- (expUriP pm)
    x <- many $ try $ apSection pm ap
    return $ Declaration annos (mkEntity AnnotationProperty ap) : concat x

apSection :: GA.PrefixMap -> AnnotationProperty -> CharParser st [Axiom]
apSection pm p = do
    pkeyword subPropertyOfC
    as <- sepByComma $ optAnnos pm (expUriP pm)
    return $ map (\(ans, i) -> AnnotationAxiom $ SubAnnotationPropertyOf ans p i) as
  <|> do
    pkeyword domainC
    as <- sepByComma $ (optAnnos pm) (expUriP pm)
    return $ map (\(ans, i) -> AnnotationAxiom $ AnnotationPropertyDomain ans p i) as
  <|> do
    pkeyword rangeC
    as <- sepByComma $ (optAnnos pm) (expUriP pm)
    return $ map (\(ans, i) -> AnnotationAxiom $ AnnotationPropertyRange ans p i) as
  <|> parseAnnotationAssertions pm (AnnSubIri p)


parseDatatypeFrame :: GA.PrefixMap -> CharParser st [Axiom]
parseDatatypeFrame pm = do
    pkeyword datatypeC
    annos <- optionalAnnos pm
    iri <- datatypeUri pm
    axs <- option [] (try $ (do
        pkeyword equivalentToC
        ans <- many $ annotations pm
        range <- dataRange pm
        return [DatatypeDefinition (concat ans) iri range]
      ) <|> parseAnnotationAssertions pm (AnnSubIri iri))
    return $ Declaration annos (mkEntity Datatype iri) : axs

classFrame :: GA.PrefixMap -> CharParser st [Axiom]
classFrame pm = do
    pkeyword classC
    annos <- optionalAnnos pm
    desc <- description pm
    axs <- many $ classFrameSection pm desc
    -- ignore Individuals: ... !
    -- optional $ pkeyword individualsC >> sepByComma (individual pm)
    return $ case desc of
      Expression i -> Declaration annos (mkEntity Class i) : concat axs
      _ -> concat axs

classFrameSection :: GA.PrefixMap -> ClassExpression -> CharParser st [Axiom]
classFrameSection pm e =
  do
    pkeyword subClassOfC
    ds <- descriptionAnnotatedList pm
    return $ map (\(anns, desc) -> ClassAxiom $ SubClassOf anns e desc) ds
  <|> do
    pkeyword equivalentToC
    ds <- descriptionAnnotatedList pm
    return $ map (\(anns, desc) -> ClassAxiom $ EquivalentClasses anns [e, desc]) ds
  <|> do
    pkeyword disjointWithC
    ds <- descriptionAnnotatedList pm
    return $ map (\(anns, desc) -> ClassAxiom $ DisjointClasses anns [e, desc]) ds
  <|> do
    pkeyword disjointUnionOfC
    as <- optionalAnnos pm
    ds <- sepByComma $ description pm
    return [ClassAxiom $ DisjointClasses as (e : ds)]
      
  <|> do
    pkeyword hasKeyC
    as <- optionalAnnos pm
    props <- parseProperties pm
    return [HasKey as e (fst props) (snd props)]
  <|> do
    -- This section is only created by the OWL API and is not defined in the standard.
    -- It only duplicates information see https://github.com/owlcs/owlapi/issues/1006
    pkeyword "Individuals:"
    sepByComma $ individual pm
    return []
  <|> case e of
    Expression i -> parseAnnotationAssertions pm (AnnSubIri i)
    _ -> unexpected "Annotation for class expression"

parseAnnotationAssertions :: GA.PrefixMap -> AnnotationSubject -> CharParser st [Axiom]
parseAnnotationAssertions pm s = do
    a <- annotations pm
    return $ (fmap (\an -> AnnotationAxiom $ AnnotationAssertion [] (annProperty an) s (annValue an)) a)

objPropExprAList :: GA.PrefixMap -> CharParser st [(Annotations, ObjectPropertyExpression)]
objPropExprAList pm = sepByComma $ optAnnos pm $ objectPropertyExpr pm

objectPropertyFrameSection :: GA.PrefixMap -> ObjectPropertyExpression -> CharParser st [Axiom]
objectPropertyFrameSection pm oe =
  do
    pkeyword domainC
    ds <- descriptionAnnotatedList pm
    return $ map (\(anns, desc) -> ObjectPropertyAxiom $ ObjectPropertyDomain anns oe desc) ds
  <|> do
    pkeyword rangeC
    ds <- descriptionAnnotatedList pm
    return $ map (\(anns, desc) -> ObjectPropertyAxiom $ ObjectPropertyRange anns oe desc) ds
  <|> do
    pkeyword characteristicsC
    ax <- sepByComma $ objectPropertyCharacter pm oe
    return $ ObjectPropertyAxiom <$> ax
  <|> do
    pkeyword subPropertyOfC
    ds <- objPropExprAList pm
    return $ map (\(anns, desc) -> ObjectPropertyAxiom $ SubObjectPropertyOf anns (SubObjPropExpr_obj oe) desc) ds
  <|> do
    pkeyword equivalentToC
    ds <- objPropExprAList pm
    return $ map (\(anns, desc) -> ObjectPropertyAxiom $ EquivalentObjectProperties anns [oe, desc]) ds
  <|> do
    pkeyword disjointWithC
    ds <- objPropExprAList pm
    return $ map (\(anns, desc) -> ObjectPropertyAxiom $ DisjointObjectProperties anns [oe, desc]) ds
  <|> do
    pkeyword inverseOfC
    ds <- objPropExprAList pm
    return $ map (\(anns, desc) -> ObjectPropertyAxiom $ InverseObjectProperties anns oe desc) ds
  <|> do
    pkeyword subPropertyChainC
    as <- optionalAnnos pm
    os <- sepBy1 (objectPropertyExpr pm) (pkeyword oS)
    return [ObjectPropertyAxiom $ SubObjectPropertyOf as (SubObjPropExpr_exprchain os) oe]
  <|> case oe of
    ObjectProp i -> parseAnnotationAssertions pm (AnnSubIri i)
    _ -> unexpected "Annotation for object property expression"

objectPropertyFrame :: GA.PrefixMap -> CharParser st [Axiom]
objectPropertyFrame pm = do
    pkeyword objectPropertyC
    annos <- optionalAnnos pm
    oe <- objectPropertyExpr pm
    sections <- many $ objectPropertyFrameSection pm oe
    return $ case oe of
      ObjectProp i -> Declaration annos (mkEntity ObjectProperty i) : concat sections
      _ -> concat sections

dataPropExprAList :: GA.PrefixMap -> CharParser st [(Annotations, DataPropertyExpression)]
dataPropExprAList pm = sepByComma $ (optAnnos pm) (expUriP pm)


dataFrameSection :: GA.PrefixMap -> DataPropertyExpression -> CharParser st [Axiom]
dataFrameSection pm de = do
    pkeyword domainC
    ds <- descriptionAnnotatedList pm
    return $ map (\(anns, desc) -> DataPropertyAxiom $ DataPropertyDomain anns de desc) ds
  <|> do
    pkeyword rangeC
    ds <- sepByComma $ (optAnnos pm) (dataRange pm)
    return $ map (\(anns, r) -> DataPropertyAxiom $ DataPropertyRange anns de r) ds
  <|> do
    pkeyword characteristicsC
    as <- optionalAnnos pm
    pkeyword functionalS
    return [DataPropertyAxiom $ FunctionalDataProperty as de]
  <|> do
    pkeyword subPropertyOfC
    ds <- dataPropExprAList pm
    return $ map (\(anns, sup) -> DataPropertyAxiom $ SubDataPropertyOf anns de sup) ds
  <|> do
    pkeyword equivalentToC
    ds <- dataPropExprAList pm
    return $ map (\(anns, d) -> DataPropertyAxiom $ EquivalentDataProperties anns [de, d]) ds
  <|> do
    pkeyword disjointWithC
    ds <- dataPropExprAList pm
    return $ map (\(anns, d) -> DataPropertyAxiom $ DisjointDataProperties anns [de, d]) ds
  <|> parseAnnotationAssertions pm (AnnSubIri de)

dataPropertyFrame :: GA.PrefixMap -> CharParser st [Axiom]
dataPropertyFrame pm = do
    pkeyword dataPropertyC
    annos <- optionalAnnos pm
    duri <- expUriP pm
    sections <- many $ dataFrameSection pm duri 
    return $ Declaration annos (mkEntity DataProperty duri) : concat sections

fact :: GA.PrefixMap -> Individual -> CharParser st Assertion
fact pm i = do
    anns <- optionalAnnos pm
    negative <- option False $ pkeyword notS >> return True
    try (do
        u <- expUriP pm
        c <- literal pm
        let assertion = if negative
            then NegativeDataPropertyAssertion
            else DataPropertyAssertion
        return $ assertion anns u i c)
      <|> do
        o <- objectPropertyExpr pm
        t <- individual pm
        let assertion = if negative
            then NegativeObjectPropertyAssertion
            else ObjectPropertyAssertion
        return $ assertion anns o i t

iFrameSection :: GA.PrefixMap -> Individual -> CharParser st [Axiom]
iFrameSection pm i = do
    pkeyword typesC
    ds <- descriptionAnnotatedList pm
    return $ map (\(ans, d) -> Assertion $ ClassAssertion ans d i) ds
  <|> do
    pkeyword sameAsC
    is <- sepByComma $ (optAnnos pm) $ individual pm
    return $ map (\(ans, d) -> Assertion $ SameIndividual ans [d, i]) is
  <|> do
    pkeyword differentFromC
    is <- sepByComma $ (optAnnos pm) $ individual pm
    return $ map (\(ans, d) -> Assertion $ DifferentIndividuals ans [d, i]) is
  <|> do
    pkeyword factsC
    facts <- sepByComma $ fact pm i
    return $ Assertion <$> facts
  <|> parseAnnotationAssertions pm (AnnSubAnInd i)

individualFrame ::GA.PrefixMap -> CharParser st [Axiom]
individualFrame pm = do
    pkeyword individualC
    annos <- optionalAnnos pm
    iuri <- individual pm
    axs <- many $ iFrameSection pm iuri
    return $ Declaration annos (mkEntity NamedIndividual iuri) :concat axs

parseEquivalentClasses :: GA.PrefixMap -> CharParser st ClassAxiom
parseEquivalentClasses pm = do
    pkeyword equivalentClassesC
    anns <- optionalAnnos pm
    classExprs <- sepByComma $ description pm
    return $ EquivalentClasses anns classExprs

parseDisjointClasses :: GA.PrefixMap -> CharParser st ClassAxiom
parseDisjointClasses pm = do
    pkeyword disjointClassesC
    anns <- optionalAnnos pm
    classExprs <- sepByComma $ description pm
    return $ DisjointClasses anns classExprs

parseEquivalentObjectProperties :: GA.PrefixMap -> CharParser st ObjectPropertyAxiom
parseEquivalentObjectProperties pm = do
    pkeyword equivalentPropertiesC
    anns <- optionalAnnos pm
    objectExprs <- sepByComma $ objectPropertyExpr pm
    return $ EquivalentObjectProperties anns objectExprs

parseDisjointObjectProperties :: GA.PrefixMap -> CharParser st ObjectPropertyAxiom
parseDisjointObjectProperties pm = do
    pkeyword disjointPropertiesC
    anns <- optionalAnnos pm
    objectExprs <- sepByComma $ objectPropertyExpr pm
    return $ DisjointObjectProperties anns objectExprs

parseSameIndividuals :: GA.PrefixMap -> CharParser st Assertion
parseSameIndividuals pm = do
    pkeyword sameIndividualC
    anns <- optionalAnnos pm
    indivs <- sepByComma $ individualUri pm
    return $ SameIndividual anns indivs


parseDifferentIndividuals :: GA.PrefixMap -> CharParser st Assertion
parseDifferentIndividuals pm = do
    pkeyword differentIndividualsC
    anns <- optionalAnnos pm
    indivs <- sepByComma $ individualUri pm
    return $ SameIndividual anns indivs


misc :: GA.PrefixMap -> CharParser st Axiom
misc pm =
    ClassAxiom <$> parseEquivalentClasses pm <|>
    ClassAxiom <$> parseDisjointClasses pm <|>
    ObjectPropertyAxiom <$> parseEquivalentObjectProperties pm <|>
    ObjectPropertyAxiom <$> parseDisjointObjectProperties pm <|>
    Assertion <$> parseSameIndividuals pm <|>
    Assertion <$> parseDifferentIndividuals pm

-- # Rules
-- There are ambiguities listed in the following table
{-

<predicate>(<iri>)                 | ClassAtom
<predicate>(<literal>)             | DataRangeAtom, BuiltInAtom
<predicate>(?<var>)                | ClassAtom, DataRangeAtom, BuiltInAtom

<predicate>(<iri>, <iri>)          | ObjectPropertyAtom
<predicate>(<literal>, <iri>)      | -invalid-
<predicate>(?<var>, <iri>)         | ObjectPropertyAtom
<predicate>(<iri>, <literal>)      | DataPropertyAtom
<predicate>(<literal>, <literal>)  | BuiltInAtom
<predicate>(?<var>, <literal>)     | ObjectPropertyAtom, DataPropertyAtom
<predicate>(<iri>, ?<var>)         | ObjectPropertyAtom, DataPropertyAtom
<predicate>(<literal>, ?<var>)     | BuiltInAtom
<predicate>(?<var>, ?<var>)        | ObjectPropertyAtom, DataPropertyAtom, BuiltInAtom

<predicate>(<any>, <any>, <any>, ...) | BuiltInAtom

-}

parseVariable :: GA.PrefixMap -> CharParser st Variable
parseVariable pm = optParensP $ do 
  char '?'
  expUriP pm

parseNoVariable :: CharParser st a -> CharParser st a
parseNoVariable p = do
  nextChar <- lookAhead anyChar
  if nextChar == '?' then Fail.fail "Variable" else p

parseClassExprAtom :: GA.PrefixMap -> CharParser st Atom
parseClassExprAtom pm = do
  classExpr <- parensP $ description pm
  arg <- (IVar <$> parseVariable pm) <|> (IArg <$> expUriP pm)
  return $ ClassAtom classExpr arg

-- parses uniquely identified class atoms. The only way a class atom can be
-- identified as such during parsing is if iArg is an individual. If it is a Variable
-- it could also be a DataRangeAtom.
parseClassAtom :: GA.PrefixMap -> IRI -> CharParser st Atom
parseClassAtom pm pre = ClassAtom (Expression pre) <$>
  (IArg <$> parseNoVariable (expUriP pm))

parseIArg :: GA.PrefixMap -> CharParser st IndividualArg
parseIArg pm = (IVar <$> parseVariable pm) <|> (IArg <$> individual pm)

parseObjectPropertyAtom :: GA.PrefixMap -> IRI -> CharParser st Atom
parseObjectPropertyAtom pm pre = do
  iarg <- parseIArg pm
  commaP
  i <- IArg <$> parseNoVariable (individual pm)
  return $ ObjectPropertyAtom (ObjectProp pre) iarg i

parseDataPropertyAtom :: GA.PrefixMap -> IRI -> CharParser st Atom
parseDataPropertyAtom pm pre = do
  iarg <- IArg <$> parseNoVariable (individual pm)
  commaP
  dataProp <- DArg <$> literal pm
  return $ DataPropertyAtom pre iarg dataProp

parseSameIndividualsAtom :: GA.PrefixMap -> CharParser st Atom
parseSameIndividualsAtom pm = do
  pkeyword sameAsS
  parensP $ do 
    iarg1 <- parseIArg pm
    commaP
    iarg2 <- parseIArg pm
    return $ SameIndividualAtom iarg1 iarg2
  
parseDifferentIndividualsAtom :: GA.PrefixMap -> CharParser st Atom
parseDifferentIndividualsAtom pm = do
  pkeyword differentFromS
  parensP $ do
    iarg1 <- parseIArg pm
    commaP
    iarg2 <- parseIArg pm
    return $ DifferentIndividualsAtom iarg1 iarg2

parseDArg :: GA.PrefixMap -> CharParser st DataArg
parseDArg pm = (DArg <$> literal pm) <|> (DVar <$> parseVariable pm)



parseBuiltInAtom :: GA.PrefixMap -> IRI -> CharParser st Atom
parseBuiltInAtom pm pre = do
  unless (isSWRLBuiltIn pre) $ Fail.fail ("\"" ++ show pre ++ "\" is not a built in predicate.")
  BuiltInAtom pre <$> sepByComma (parseDArg pm)


parseUnknownArg :: GA.PrefixMap -> CharParser st UnknownArg
parseUnknownArg pm = (Variable <$> parseVariable pm) <|>
  try (IndividualArg <$> parseIArg pm) <|>
  (DataArg <$> parseDArg pm)

parseUnknownAtom :: GA.PrefixMap -> IRI -> CharParser st Atom
parseUnknownAtom pm pre =
  try (UnknownBinaryAtom pre <$> parseUnknownArg pm <*> (commaP >> parseUnknownArg pm)) <|>
  (UnknownUnaryAtom pre <$> parseUnknownArg pm)

parseDataRangeAtom :: GA.PrefixMap -> IRI -> CharParser st Atom
parseDataRangeAtom pm pre = do
  facets <- parseFacetValuePairs pm
  darg <- parseDArg pm
  return $ DataRangeAtom (DataType pre facets) darg


parseAtom :: GA.PrefixMap -> CharParser st Atom
parseAtom pm =  parseClassExprAtom pm <|> 
  parseSameIndividualsAtom pm <|>
  parseDifferentIndividualsAtom pm <|> do
    pre <- expUriP pm
    choice $ map try [
      parensP $ parseBuiltInAtom pm pre,
      parensP $ parseClassAtom pm pre,
      parensP $ parseDataPropertyAtom pm pre,
      parensP $ parseObjectPropertyAtom pm pre,
      parseDataRangeAtom pm pre,
      parensP $ parseUnknownAtom pm pre]

parseRule :: GA.PrefixMap -> CharParser st Axiom
parseRule pm = do
  pkeyword ruleC
  anns <- optionalAnnos pm
  body <- sepByComma (parseAtom pm) 
  pkeyword "->"
  rHead <- sepByComma (parseAtom pm)
  return $ Rule $ DLSafeRule anns body rHead


parseFrame :: GA.PrefixMap -> CharParser st [Axiom]
parseFrame pm = do 
  frames <- classFrame pm <|> parseDatatypeFrame pm
    <|> objectPropertyFrame pm <|> dataPropertyFrame pm <|> individualFrame pm
    <|> annotationPropertyFrame pm <|> (misc pm >>= return.return)
    <|> (parseRule pm >>= return.return)
  return $ frames


importEntry :: GA.PrefixMap -> CharParser st DirectlyImportsDocuments
importEntry pm = many $ pkeyword importC >> expUriP pm

parseOntology :: GA.PrefixMap -> CharParser st Ontology
parseOntology pm = do
    (ontologyIRI, versionIRI) <- option (Nothing, Nothing) (do 
        pkeyword ontologyC
        o <- optionMaybe (expUriP pm)
        v <- optionMaybe (expUriP pm)
        return (o, v)
      )
    imports <- importEntry pm
    anns <- optionalAnnos pm
    axs <- many $ parseFrame pm
    case (ontologyIRI, versionIRI, imports, anns, axs) of
      (Nothing, Nothing, [], [], []) -> unexpected "empty ontology"
      _ -> return $ Ontology ontologyIRI versionIRI imports anns (concat axs)
  

parsePrefixDeclaration :: CharParser st (String, IRI)
parsePrefixDeclaration =  do
    pkeyword prefixC
    p <- skips (option "" prefix << char ':')
    i <- skips fullIri
    return $ (p, i)
  <|> do
    pkeyword namespaceC
    p <- skips prefix
    i <- skips fullIri
    return $ (p, i)

parseOntologyDocument :: GA.PrefixMap -> CharParser st OntologyDocument
parseOntologyDocument gapm = do
    skipMany (forget space <|> forget comment)
    prefixes <- many parsePrefixDeclaration
    let pm = Map.unions [gapm, (Map.fromList prefixes), predefPrefixesGA]
    o <- parseOntology pm
    return $ OntologyDocument (OntologyMetadata MS) pm o

