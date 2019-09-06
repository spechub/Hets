{- |
Module      :  ./OWL2/ManchesterParser.hs
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Manchester Syntax parser

References  :  <http://www.w3.org/TR/2009/NOTE-owl2-manchester-syntax-20091027/>
-}

module OWL2.ManchesterParser where

import OWL2.AS
import OWL2.MS
import OWL2.Parse
import OWL2.Keywords
import OWL2.ColonKeywords

import Common.IRI
import Common.Keywords
import Common.Parsec
import qualified Common.GlobalAnnotations as GA (PrefixMap)

import Text.ParserCombinators.Parsec
import qualified Data.Map as Map

import Debug.Trace

optAnnos :: CharParser st a -> CharParser st (Annotations, a)
optAnnos p = do
    as <- optionalAnnos
    a <- p
    return (as, a)

optionalAnnos :: CharParser st Annotations
optionalAnnos = option [] annotations

annotations :: CharParser st Annotations
annotations = do
    pkeyword annotationsC
    fmap (map $ \ (as, (i, v)) -> Annotation as i v)
     . sepByComma . optAnnos $ pair uriP annotationValue

descriptionAnnotatedList :: Bool -> CharParser st [(Annotations, ClassExpression)]
descriptionAnnotatedList flag = sepByComma $ optAnnos (description flag)

makeFrame :: Extended -> [FrameBit] -> Frame
makeFrame ext fbl = Frame ext
    $ if null fbl then
        [AnnFrameBit [] $ AnnotationFrameBit Declaration]
      else fbl

annotationPropertyFrame :: CharParser st Frame
annotationPropertyFrame = do
    pkeyword annotationPropertyC
    ap <- uriP
    x <- many apBit
    return $ makeFrame (SimpleEntity $ mkEntity AnnotationProperty ap) x

apBit :: CharParser st FrameBit
apBit = do
    pkeyword subPropertyOfC
    x <- sepByComma $ optAnnos uriP
    return $ ListFrameBit (Just SubPropertyOf) $ AnnotationBit x
  <|> do
    dr <- domainOrRange
    x <- sepByComma $ optAnnos uriP
    return $ ListFrameBit (Just $ DRRelation dr) $ AnnotationBit x
  <|> do
    x <- annotations
    return $ AnnFrameBit x $ AnnotationFrameBit Assertion

datatypeBit :: CharParser st Frame
datatypeBit = do
    pkeyword datatypeC
    duri <- datatypeUri
    as1 <- many annotations
    mp <- optionMaybe $ pkeyword equivalentToC >> pair optionalAnnos dataRange
    as2 <- many annotations
    return $ Frame (SimpleEntity $ mkEntity Datatype duri)
      $ map (`AnnFrameBit` AnnotationFrameBit Assertion) as1 ++ case mp of
          Nothing -> [AnnFrameBit [] $ AnnotationFrameBit Declaration]
          Just (ans, dr) -> [AnnFrameBit ans $ DatatypeBit dr]
        ++ map (`AnnFrameBit` AnnotationFrameBit Assertion) as2

classFrame :: Bool -> CharParser st Frame
classFrame flag = do
    pkeyword classC
    i <- description flag
    plain <- many (classFrameBit flag) 
    -- ignore Individuals: ... !
    optional $ pkeyword individualsC >> sepByComma individual
    return $ makeFrame (ClassEntity i) plain

classFrameBit :: Bool -> CharParser st FrameBit
classFrameBit flag = do
    pkeyword subClassOfC
    ds <- descriptionAnnotatedList flag
    return $ ListFrameBit (Just SubClass) $ ExpressionBit ds
  <|> do
    e <- equivOrDisjoint
    ds <- descriptionAnnotatedList flag
    return $ ListFrameBit (Just $ EDRelation e) $ ExpressionBit ds
  <|> do
    pkeyword disjointUnionOfC
    as <- optionalAnnos
    ds <- sepByComma (description flag)
    return $ AnnFrameBit as $ ClassDisjointUnion ds
  <|> do
    pkeyword hasKeyC
    as <- optionalAnnos
    o <- sepByComma (objectPropertyExpr flag)
    return $ AnnFrameBit as $ ClassHasKey o []
  <|> do
    as <- annotations
    return $ AnnFrameBit as $ AnnotationFrameBit Assertion

objPropExprAList :: Bool -> CharParser st [(Annotations, ObjectPropertyExpression)]
objPropExprAList flag = sepByComma $ optAnnos (objectPropertyExpr flag)

objectFrameBit :: Bool -> CharParser st FrameBit
objectFrameBit flag = do
    r <- domainOrRange
    ds <- descriptionAnnotatedList flag
    return $ ListFrameBit (Just $ DRRelation r) $ ExpressionBit ds
  <|> do
    characterKey
    ds <- sepByComma $ optAnnos objectPropertyCharacter
    return $ ListFrameBit Nothing $ ObjectCharacteristics ds
  <|> do
    subPropertyKey
    ds <- objPropExprAList flag
    return $ ListFrameBit (Just SubPropertyOf) $ ObjectBit ds
  <|> do
    e <- equivOrDisjoint
    ds <- objPropExprAList flag
    return $ ListFrameBit (Just $ EDRelation e) $ ObjectBit ds
  <|> do
    pkeyword inverseOfC
    ds <- objPropExprAList flag
    return $ ListFrameBit (Just InverseOf) $ ObjectBit ds
  <|> do
    pkeyword subPropertyChainC
    as <- optionalAnnos
    os <- sepBy1 (objectPropertyExpr flag) (keyword oS)
    return $ AnnFrameBit as $ ObjectSubPropertyChain os
  <|> do
    as <- annotations
    return $ AnnFrameBit as $ AnnotationFrameBit Assertion

objectPropertyFrame :: Bool -> CharParser st Frame
objectPropertyFrame flag = do
    pkeyword objectPropertyC
    ouri <- objectPropertyExpr flag
    as <- many (objectFrameBit flag)
    return $ makeFrame (ObjectEntity ouri) as

dataPropExprAList :: CharParser st [(Annotations, DataPropertyExpression)]
dataPropExprAList = sepByComma $ optAnnos uriP

dataFrameBit :: Bool -> CharParser st FrameBit
dataFrameBit flag = do
    pkeyword domainC
    ds <- descriptionAnnotatedList flag
    return $ ListFrameBit (Just (DRRelation ADomain)) $ ExpressionBit ds
  <|> do
    pkeyword rangeC
    ds <- sepByComma $ optAnnos dataRange
    return $ ListFrameBit Nothing $ DataPropRange ds
  <|> do
    characterKey
    as <- optionalAnnos
    keyword functionalS
    return $ AnnFrameBit as DataFunctional
  <|> do
    subPropertyKey
    ds <- dataPropExprAList
    return $ ListFrameBit (Just SubPropertyOf) $ DataBit ds
  <|> do
    e <- equivOrDisjoint
    ds <- dataPropExprAList
    return $ ListFrameBit (Just (EDRelation e)) $ DataBit ds
  <|> do
    as <- annotations
    return $ AnnFrameBit as $ AnnotationFrameBit Assertion

dataPropertyFrame :: Bool -> CharParser st Frame
dataPropertyFrame flag = do
    pkeyword dataPropertyC
    duri <- uriP
    as <- many (dataFrameBit flag)
    return $ makeFrame (SimpleEntity $ mkEntity DataProperty duri) as

fact :: CharParser st Fact
fact = do
    pn <- option Positive $ keyword notS >> return Negative
    u <- uriP
    do
        c <- literal
        return $ DataPropertyFact pn u c
      <|> do
        t <- individual
        return $ ObjectPropertyFact pn (ObjectProp u) t

iFrameBit :: Bool -> CharParser st FrameBit
iFrameBit flag = do
    pkeyword typesC
    ds <- descriptionAnnotatedList flag
    return $ ListFrameBit (Just Types) $ ExpressionBit ds
  <|> do
    s <- sameOrDifferent
    is <- sepByComma $ optAnnos individual
    return $ ListFrameBit (Just $ SDRelation s) $ IndividualSameOrDifferent is
  <|> do
    pkeyword factsC
    fs <- sepByComma $ optAnnos fact
    return $ ListFrameBit Nothing $ IndividualFacts fs
  <|> do
    a <- annotations
    return $ AnnFrameBit a $ AnnotationFrameBit Assertion

individualFrame :: Bool -> CharParser st Frame
individualFrame flag = do
    pkeyword individualC
    iuri <- individual
    as <- many (iFrameBit flag)
    let ent = if flag then SimpleEntity $ mkEntity NamedIndividual iuri
              else SimpleEntity $ mkEntity UnsolvedEntity iuri
    return $ makeFrame ent as

misc :: Bool -> CharParser st Frame
misc flag = do
    e <- equivOrDisjointKeyword classesC
    as <- optionalAnnos
    ds <- sepByComma (description flag)
    return $ Frame (Misc as) [ListFrameBit (Just $ EDRelation e)
        $ ExpressionBit $ emptyAnnoList ds]
  <|> do
    e <- equivOrDisjointKeyword propertiesC
    as <- optionalAnnos
    es <- sepByComma (objectPropertyExpr flag)
    -- indistinguishable from dataProperties
    return $ Frame (Misc as) [ListFrameBit (Just $ EDRelation e)
        $ ObjectBit $ emptyAnnoList es]
  <|> do
    s <- sameOrDifferentIndu
    as <- optionalAnnos
    is <- sepByComma individualUri
    return $ Frame (Misc as) [ListFrameBit (Just $ SDRelation s)
        $ IndividualSameOrDifferent $ emptyAnnoList is]

frames :: Bool -> CharParser st [Frame]
frames flag = 
        many $ datatypeBit <|> classFrame flag
    <|> objectPropertyFrame flag <|> dataPropertyFrame flag <|> individualFrame flag
    <|> annotationPropertyFrame <|> misc flag

-- the Bool flag is true for ontologies and false for macros
basicSpec :: Bool -> GA.PrefixMap -> CharParser st OntologyDocument
basicSpec flag pm = do
    nss <- many nsEntry
    ou <- option nullIRI $ pkeyword ontologyC >> option nullIRI uriP
    ie <- many importEntry
    ans <- many annotations
    as <- frames flag
    if null nss && null ie && null ans && null as && ou == nullIRI
      then fail "empty ontology"
      else do 
       let o = OntologyDocument
                 (Map.union (Map.fromList $ map (\ (p, q) -> (p, showIRICompact q)) nss)
                  (convertPrefixMap pm))
                 (emptyOntology as)
                  { imports = ie
                  , ann = ans
                  , name = ou }
       -- trace ("o:" ++ show o) $ 
       return o
