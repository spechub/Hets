{- |
Module      :  $Header$
ClassExpression :  Manchester syntax parser for OWL 2
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Parser from Manchester Syntax to Manchester Abstract Syntax
<http://www.w3.org/TR/2009/NOTE-owl2-manchester-syntax-20091027/>
-}

module OWL2.ManchesterParser where

import OWL2.AS
import OWL2.MS
import OWL2.Parse
import OWL.Keywords
import OWL.ColonKeywords

import Common.Keywords
import Common.Parsec

import Text.ParserCombinators.Parsec
import qualified Data.Map as Map

objectPropertyCharacter :: CharParser st Character
objectPropertyCharacter =
  choice $ map (\ f -> keyword (show f) >> return f) characters

optAnnos :: CharParser st a -> CharParser st (Annotations, a)
optAnnos p = do
  as <- option noAnnos $ annotations
  a <- p
  return (as, a)

annotations :: CharParser st Annotations
annotations = do
   pkeyword annotationsC
   fmap Annotations $ sepByComma $ optAnnos annotation

descriptionAnnotatedList :: CharParser st [(Annotations, ClassExpression)]
descriptionAnnotatedList = sepByComma $ optAnnos description

annotationPropertyFrame :: CharParser st [Frame]
annotationPropertyFrame = do
  pkeyword annotationPropertyC
  ap <- uriP
  x <- flat $ many $ apBit
  return [Frame (Entity AnnotationProperty ap) x]

apBit :: CharParser st [FrameBit]
apBit = do
          pkeyword subPropertyOfC
          x <- sepByComma $ optAnnos uriP
          return [AnnotationBit SubPropertyOf $ AnnotatedList x]
        <|> do
          pkeyword rangeC
          x <- sepByComma $ optAnnos uriP
          return [AnnotationBit Range $ AnnotatedList x ]
       <|> do
          pkeyword domainC
          x <- sepByComma $ optAnnos uriP
          return [AnnotationBit Domain $ AnnotatedList x ]
       <|> do
          x <- annotations
          return [AnnotationFrameBit x]

datatypeFrame :: CharParser st [Frame]
datatypeFrame = do
    pkeyword datatypeC
    duri <- datatypeUri
    x <- many annotations
    ms <- optionMaybe $ do
      pkeyword equivalentToC
      al <- option noAnnos annotations
      dr <- dataRange
      return (al, dr)
    y <- many annotations
    return [Frame (Entity Datatype duri) [DatatypeFrame x ms y]]

classFrame :: CharParser st [Frame]
classFrame = do
        pkeyword classC
        iri <- uriP
        plain <- flat $ many $ classFrameBit
        if null plain then return [Frame (Entity Class iri) []]
                      else return [Frame (Entity Class iri) plain]

classFrameBit ::CharParser st [FrameBit]
classFrameBit = do
    pkeyword subClassOfC
    ds <- descriptionAnnotatedList
    return [ExpressionBit SubClass $ AnnotatedList ds]
  <|> do
    e <- equivOrDisjoint
    ds <- descriptionAnnotatedList
    return [ExpressionBit e $ AnnotatedList ds]
  <|> do
    pkeyword disjointUnionOfC
    as <- option noAnnos annotations
    ds <- sepByComma description
    return [ClassDisjointUnion as ds]
  <|> do
    pkeyword hasKeyC
    as <- option noAnnos annotations
    o <- sepByComma objectPropertyExpr
    return [ClassHasKey as o []]
  <|> do
    as <- annotations
    return [AnnotationFrameBit as]

objPropExprAList :: CharParser st [(Annotations, ObjectPropertyExpression)]
objPropExprAList = sepByComma $ optAnnos objectPropertyExpr

relation :: CharParser st EquivOrDisjoint
relation = choice
  $ map (\ f -> pkeyword (showEquivOrDisjoint f) >> return f)
  equivOrDisjointL

objectFrameBit :: CharParser st [FrameBit]
objectFrameBit = do
    r <- relation
    ds <- descriptionAnnotatedList
    return [ExpressionBit r $ AnnotatedList ds]
  <|> do
    characterKey
    ds <- sepByComma $ optAnnos objectPropertyCharacter
    return [ObjectCharacteristics $ AnnotatedList ds]
  <|> do
    subPropertyKey
    ds <- objPropExprAList
    return [ObjectBit SubPropertyOf $ AnnotatedList ds]
  <|> do
    e <- equivOrDisjoint
    ds <- objPropExprAList
    return [ObjectBit e $ AnnotatedList ds]
  <|> do
    pkeyword inverseOfC
    ds <- objPropExprAList
    return [ObjectBit InverseOf $ AnnotatedList ds]
  <|> do
    pkeyword subPropertyChainC
    as <- option noAnnos annotations
    os <- sepBy1 objectPropertyExpr (keyword oS)
    return [ObjectSubPropertyChain as os]
  <|> do
    as <- annotations
    return [AnnotationFrameBit as]

objectPropertyFrame :: CharParser st [Frame]
objectPropertyFrame = do
  pkeyword objectPropertyC
  ouri <- uriP
  as <- flat $ many $ objectFrameBit
  return $ if null as
    then [Frame (Entity ObjectProperty ouri) []]
    else [Frame (Entity ObjectProperty ouri) as]

dataPropExprAList :: CharParser st [(Annotations, DataPropertyExpression)]
dataPropExprAList = sepByComma $ optAnnos uriP

dataFrameBit :: CharParser st [FrameBit]
dataFrameBit  = do
    pkeyword domainC
    ds <- descriptionAnnotatedList
    return [ExpressionBit Domain $ AnnotatedList ds]
  <|> do
    pkeyword rangeC
    ds <- sepByComma $ optAnnos dataRange
    return [DataPropRange $ AnnotatedList ds]
  <|> do
    characterKey
    as <- option noAnnos annotations
    keyword functionalS
    return [DataFunctional as]
  <|> do
    subPropertyKey
    ds <- dataPropExprAList
    return [DataBit SubPropertyOf $ AnnotatedList ds]
  <|> do
    e <- equivOrDisjoint
    ds <- dataPropExprAList
    return [DataBit e $ AnnotatedList ds]
  <|> do
    as <- annotations
    return [AnnotationFrameBit as]

dataPropertyFrame :: CharParser st [Frame]
dataPropertyFrame = do
  pkeyword dataPropertyC
  duri <- uriP
  as <- flat $ many $ dataFrameBit
  return $ if null as
    then [Frame (Entity DataProperty duri) []]
    else [Frame (Entity DataProperty duri) as]

fact :: CharParser st Fact
fact = do
  pn <- option Positive $ keyword notS >> return Negative
  u <- uriP
  do
      c <- literal
      return $ DataPropertyFact pn u c
    <|> do
      t <- individualUri
      return $ ObjectPropertyFact pn (ObjectProp u) t

iFrameBit :: CharParser st [FrameBit]
iFrameBit = do
    pkeyword typesC
    ds <- descriptionAnnotatedList
    return [ExpressionBit Types $ AnnotatedList ds]
  <|> do
    s <- sameOrDifferent
    is <- sepByComma $ optAnnos individualUri
    return [IndividualSameOrDifferent s $ AnnotatedList is]
  <|> do
    pkeyword factsC
    fs <- sepByComma $ optAnnos $ fact
    return [IndividualFacts $ AnnotatedList fs]
  <|> do
    a <- annotations
    return [AnnotationFrameBit a]

individualFrame :: CharParser st [Frame]
individualFrame = do
  pkeyword individualC
  iuri <- individualUri
  as <- flat $ many $ iFrameBit
  return $ if null as
    then [Frame (Entity NamedIndividual iuri) []]
    else [Frame (Entity NamedIndividual iuri) as]

misc :: CharParser st Frame
misc = do
    e <- equivOrDisjointKeyword classesC
    as <- option noAnnos annotations
    ds <- sepByComma description
    return $ MiscFrame $ MiscEquivOrDisjointClasses e as ds
  <|> do
    e <- equivOrDisjointKeyword propertiesC
    as <- option noAnnos annotations
    es <- sepByComma objectPropertyExpr
    -- indistinguishable from dataProperties
    return $ MiscFrame $ MiscEquivOrDisjointObjProp e as es
  <|> do
    s <- sameOrDifferentIndu
    as <- option noAnnos annotations
    is <- sepByComma individualUri
    return $ MiscFrame $ MiscSameOrDifferent s as is

frames :: CharParser st [Frame]
frames = flat $ many $ datatypeFrame <|> classFrame
  <|> objectPropertyFrame <|> dataPropertyFrame <|> individualFrame
  <|> annotationPropertyFrame <|> single misc

basicSpec :: CharParser st OntologyDocument
basicSpec = do
  nss <- many nsEntry
  ou <- option dummyQName $ pkeyword ontologyC >> uriP
  ie <- many importEntry
  ans <- many annotations
  as <- frames
  return emptyOntologyDoc
    { mOntology = emptyOntologyD
      { ontologyFrame = as
      , imports = ie
      , ann = ans
      , muri = ou }
    , prefixDeclaration = Map.fromList $
      [ ("owl", "http://www.w3.org/2002/07/owl#")
      , ("rdf", "http://www.w3.org/1999/02/22-rdf-syntax-ns#")
      , ("rdfs", "http://www.w3.org/2000/01/rdf-schema#")
      , ("xsd", "http://www.w3.org/2001/XMLSchema#")
--      , ("", showQU dummyQName ++ "#") -- uncomment for API v3
      , ("owl2xml", "http://www.w3.org/2006/12/owl2-xml#") ]
      ++ map (\ (p, q) -> (p, showQU q)) nss }

