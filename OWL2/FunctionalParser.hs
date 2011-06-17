{- |
Module      :  $Header$
ClassExpression :  Manchester syntax parser for OWL 2
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Parser from Manchester Syntax to Functional Syntax
<http://www.w3.org/TR/2009/NOTE-owl2-manchester-syntax-20091027/>
-}

module OWL2.FunctionalParser where

import OWL2.Parse
import OWL2.FS
import OWL2.AS
import OWL.Keywords
import OWL.ColonKeywords

import Common.Keywords
import Common.Parsec

import Text.ParserCombinators.Parsec
import qualified Data.Map as Map

objectPropertyCharacter :: CharParser st Character
objectPropertyCharacter =
  choice $ map (\ f -> keyword (show f) >> return f) characters

optAnnos :: CharParser st a -> CharParser st ([Annotation], a)
optAnnos p = do
  as <- annotationList
  a <- p
  return (as, a)

descriptionAnnotatedList :: CharParser st [([Annotation], ClassExpression)]
descriptionAnnotatedList = sepByComma $ optAnnos description

annotationPropertyFrame :: CharParser st [Axiom]
annotationPropertyFrame = do
  pkeyword annotationPropertyC
  ap <- uriP
  x <- flat $ many $ apBit ap
  return x

apBit :: QName -> CharParser st [Axiom]
apBit ap = do
          pkeyword subPropertyOfC
          x <- sepByComma $ optAnnos uriP
          return $ map (\ (ans, iri) -> EntityAnno $ SubAnnotationPropertyOf ans ap iri) x
        <|> do
          pkeyword rangeC
          x <- sepByComma $ optAnnos uriP
          return $ map (\ (ans, iri) -> EntityAnno $ AnnotationPropertyDomainOrRange AnnRange ans ap iri) x
       <|> do
          pkeyword domainC
          x <- sepByComma $ optAnnos uriP
          return $ map (\ (ans, iri) -> EntityAnno $ AnnotationPropertyDomainOrRange AnnDomain ans ap iri) x
       <|> do
          x <- realAnnotations
          return [EntityAnno $ AnnotationAssertion x ap]

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

objPropExprAList :: CharParser st [([Annotation], ObjectPropertyExpression)]
objPropExprAList = sepByComma $ optAnnos objectPropertyExpr

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
    pkeyword individualC <|> pkeyword individualsC 
    iuri <- individualUri
    as <- flat $ many $ iFrameBit iuri
    return $ if null as
      then [PlainAxiom [] $ Declaration $ Entity NamedIndividual iuri]
      else as

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

frames :: CharParser st [Axiom]
frames = flat $ many (datatypeFrame <|> classFrame
  <|> objectPropertyFrame <|> dataPropertyFrame <|> individualFrame
  <|> annotationPropertyFrame <|> single misc)

ontologyFile :: CharParser st OntologyFile
ontologyFile = do
  nss <- many nsEntry
  ouri <- pkeyword ontologyC >> uriP
  is <- many importEntry
  as <- frames
  return emptyOntologyFile
    { ontology = (emptyOntologyByName ouri)
        { axiomsList = as
        , importsList = is }
    , prefixName = Map.fromList $ map (\ (p, q) -> (p, showQU q)) nss }

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
