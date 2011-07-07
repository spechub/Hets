module OWL2.XML where

import Text.XML.Light
import Data.Maybe
import OWL2.AS
import OWL2.MS
import Common.Lexer

getName :: Element -> String
getName (Element {elName = QName {qName = n}}) = n

getIRI :: Element -> OWL2.AS.QName
getIRI (Element {elAttribs = a}) =
        let Attr {attrVal = iri} = head a
        in mkQName iri

getInt :: Element -> Int
getInt (Element {elAttribs = a}) =
        let Attr {attrVal = int} = head a
        in value 10 int

isSmth :: String -> Text.XML.Light.QName -> Bool
isSmth s (QName {qName = qn}) = qn == s

isSmthList :: [String] -> Text.XML.Light.QName -> Bool
isSmthList l (QName {qName = qn}) = qn `elem` l

filterCh :: String -> Element -> [Element]
filterCh s = filterChildrenName (isSmth s)

filterChL :: [String] -> Element -> [Element]
filterChL l = filterChildrenName (isSmthList l)

entityList :: [String]
entityList = ["Class", "Datatype", "NamedIndividual",
    "ObjectProperty", "DataProperty", "AnnotationProperty"]

individualList :: [String]
individualList = ["NamedIndividual", "AnonymousIndividual"]

objectPropList :: [String]
objectPropList = ["ObjectProperty", "ObjectInverseOf"]

dataPropList :: [String]
dataPropList = ["DataProperty"]

dataRangeList :: [String]
dataRangeList = ["Datatype", "DatatypeRestriction", "DataComplementOf",
      "DataOneOf", "DataIntersectionOf", "DataUnionOf"]

classExpressionList :: [String]
classExpressionList = ["Class", "ObjectIntersectionOf", "ObjectUnionOf",
     "ObjectComplementOf", "ObjectOneOf", "ObjectSomeValuesFrom",
     "ObjectAllValuesFrom", "ObjectHasValue", "ObjectHasSelf",
     "ObjectMinCardinality", "ObjectMaxCardinality", "ObjectExactCardinality",
     "DataSomeValuesFrom", "DataAllValuesFrom", "DataHasValue",
     "DataMinCardinality", "DataMaxCardinality", "DataExactCardinality"]

getEntityType :: String -> EntityType
getEntityType ty = case ty of
    "Class" -> Class
    "Datatype" -> Datatype
    "NamedIndividual" -> NamedIndividual
    "ObjectProperty" -> ObjectProperty
    "DataProperty" -> DataProperty
    "AnnotationProperty" -> AnnotationProperty
    _ -> error "not entity type"

toEntity :: Element -> Entity
toEntity e = Entity (getEntityType $ getName e) (getIRI e)

getEntity :: Element -> Entity
getEntity e = toEntity $ fromJust $ filterElementName (isSmthList entityList) e

getDeclaration :: Element -> Frame
getDeclaration e =
   let ent = fromJust $ filterChildName (isSmthList entityList) e
       ans = getAllAnnos e
   in Frame (SimpleEntity $ toEntity ent) [AnnFrameBit ans AnnotationFrameBit]

getDeclarations :: Element -> [Frame]
getDeclarations e =
   let dcl = filterElementsName (isSmth "Declaration") e
   in map getDeclaration dcl

isPlainLiteral :: String -> Bool
isPlainLiteral s = "PlainLiteral" == drop (length s - 12) s

getLiteral :: Element -> Literal
getLiteral e = let lit = fromJust $ filterElementName (isSmth "Literal") e
                   lf = strContent e
                   dt = fromJust $ findAttrBy (isSmth "datatypeIRI") lit
               in
                  case findAttrBy (isSmth "lang") lit of
                    Just lang -> Literal lf (Untyped $ Just lang)
                    Nothing -> if isPlainLiteral dt then
                                  Literal lf (Untyped Nothing)
                                else Literal lf (Typed $ mkQName dt)

getValue :: Element -> AnnotationValue
getValue e = let lit = filterElementName (isSmth "Literal") e
                 val = strContent e
             in case lit of
                  Nothing -> AnnValue $ mkQName val
                  Just _ -> AnnValLit $ getLiteral e

getAnnotation :: Element -> Annotation
getAnnotation e =
     let hd = filterCh "Annotation" e
         ap = filterCh "AnnotationProperty" e
         av = filterCh "Literal" e ++ filterCh "IRI" e
     in
          Annotation (getAnnotations hd)
              (getIRI $ head ap) (getValue $ head av)

getAnnotations :: [Element] -> [Annotation]
getAnnotations e = map getAnnotation $ concatMap
            (filterElementsName (isSmth "Annotation")) e

getAllAnnos :: Element -> [Annotation]
getAllAnnos e = map getAnnotation
            $ filterElementsName (isSmth "Annotation") e

 -- still need to cancel double inverses
getObjProp :: Element -> ObjectPropertyExpression
getObjProp e = case filterElementName (isSmth "ObjectInverseOf") e of
                  Nothing -> ObjectProp $ getIRI e
                  Just _ -> ObjectInverseOf $ getObjProp $ head $ elChildren e

getFacetValuePair :: Element -> (ConstrainingFacet, RestrictionValue)
getFacetValuePair e = (getIRI e, getLiteral $ head $ elChildren e)

getDataRange :: Element -> DataRange
getDataRange e = case getName e of
    "Datatype" -> DataType (getIRI e) []
    "DatatypeRestriction" ->
        let dt = getIRI $ fromJust $ filterChildName (isSmth "Datatype") e
            fvp = map getFacetValuePair
               $ filterCh "FacetRestriction" e
        in DataType dt fvp
    "DataComplementOf" -> DataComplementOf
            $ getDataRange $ head $ elChildren e
    "DataOneOf" -> DataOneOf
            $ map getLiteral $ filterCh "Literal" e
    "DataIntersectionOf" -> DataJunction IntersectionOf
            $ map getDataRange $ elChildren e
    "DataUnionOf" -> DataJunction UnionOf
            $ map getDataRange $ elChildren e
    _ -> error "XML parser: not data range"

getClassExpression :: Element -> ClassExpression
getClassExpression e =
  let ch = elChildren e
  in case getName e of
    "Class" -> Expression $ getIRI e
    "ObjectIntersectionOf" -> ObjectJunction IntersectionOf
            $ map getClassExpression ch
    "ObjectUnionOf" -> ObjectJunction UnionOf
            $ map getClassExpression ch
    "ObjectComplementOf" -> ObjectComplementOf
            $ getClassExpression $ head ch
    "ObjectOneOf" -> ObjectOneOf
            $ map getIRI ch
    "ObjectSomeValuesFrom" -> ObjectValuesFrom SomeValuesFrom
            (getObjProp $ head ch) (getClassExpression $ last ch)
    "ObjectAllValuesFrom" -> ObjectValuesFrom AllValuesFrom
            (getObjProp $ head ch) (getClassExpression $ last ch)
    "ObjectHasValue" -> ObjectHasValue (getObjProp $ head ch) (getIRI $ last ch)
    "ObjectHasSelf" -> ObjectHasSelf $ getObjProp $ head ch
    "ObjectMinCardinality" -> if length ch == 2 then
          ObjectCardinality $ Cardinality
              MinCardinality (getInt e) (getObjProp $ head ch)
                $ Just $ getClassExpression $ last ch
         else ObjectCardinality $ Cardinality
              MinCardinality (getInt e) (getObjProp $ head ch) Nothing
    "ObjectMaxCardinality" -> if length ch == 2 then
          ObjectCardinality $ Cardinality
              MaxCardinality (getInt e) (getObjProp $ head ch)
                $ Just $ getClassExpression $ last ch
         else ObjectCardinality $ Cardinality
              MaxCardinality (getInt e) (getObjProp $ head ch) Nothing
    "ObjectExactCardinality" -> if length ch == 2 then
          ObjectCardinality $ Cardinality
              ExactCardinality (getInt e) (getObjProp $ head ch)
                $ Just $ getClassExpression $ last ch
         else ObjectCardinality $ Cardinality
              ExactCardinality (getInt e) (getObjProp $ head ch) Nothing
    "DataSomeValuesFrom" ->
        let dp = map getIRI $ init ch
            dr = last ch
        in DataValuesFrom SomeValuesFrom (head dp) (tail dp) (getDataRange dr)
    "DataAllValuesFrom" ->
        let dp = map getIRI $ init ch
            dr = last ch
        in DataValuesFrom AllValuesFrom (head dp) (tail dp) (getDataRange dr)
    "DataHasValue" -> DataHasValue (getIRI $ head ch) (getLiteral $ last ch)
    "DataMinCardinality" -> if length ch == 2 then
          DataCardinality $ Cardinality
              MinCardinality (getInt e) (getIRI $ head ch)
                $ Just $ getDataRange $ last ch
         else DataCardinality $ Cardinality
              MinCardinality (getInt e) (getIRI $ head ch) Nothing
    "DataMaxCardinality" -> if length ch == 2 then
          DataCardinality $ Cardinality
              MaxCardinality (getInt e) (getIRI $ head ch)
                $ Just $ getDataRange $ last ch
         else DataCardinality $ Cardinality
              MaxCardinality (getInt e) (getIRI $ head ch) Nothing
    "DataExactCardinality" -> if length ch == 2 then
          DataCardinality $ Cardinality
              ExactCardinality (getInt e) (getIRI $ head ch)
                $ Just $ getDataRange $ last ch
         else DataCardinality $ Cardinality
              ExactCardinality (getInt e) (getIRI $ head ch) Nothing
    _ -> error "XML parser: not ClassExpression"

getClassAxiom :: Element -> Axiom
getClassAxiom e =
   let ch = elChildren e
       as = concatMap getAllAnnos ch
       l = filterChL classExpressionList e
       drl = filterChL dataRangeList e
       cel = map getClassExpression l
   in case getName e of
    "SubClassOf" ->
       let ces = drop (length ch - 2) ch
           sub = head ces
           super = last ces
       in PlainAxiom (ClassEntity $ getClassExpression sub)
        $ ListFrameBit (Just SubClass) $ ExpressionBit
                      [(as, getClassExpression super)]
    "EquivalentClasses" -> PlainAxiom (Misc as) $ ListFrameBit
      (Just (EDRelation Equivalent)) $ ExpressionBit
          $ map (\ x -> ([], x)) cel
    "DisjointClasses" -> PlainAxiom (Misc as) $ ListFrameBit
      (Just (EDRelation Disjoint)) $ ExpressionBit
          $ map (\ x -> ([], x)) cel
    "DisjointUnion" -> PlainAxiom (SimpleEntity $ getEntity $ head l)
        $ AnnFrameBit as $ ClassDisjointUnion $ map getClassExpression $ tail l
    "DatatypeDefinition" -> PlainAxiom (SimpleEntity $ getEntity $ head drl)
        $ AnnFrameBit as $ DatatypeBit $ getDataRange $ last drl
    _ -> error "XML parser: not class axiom"

hasKey :: Element -> Axiom
hasKey e =
   let as = concatMap getAllAnnos $ elChildren e
       ce = getClassExpression $ head $ filterChL classExpressionList e
       op = map getObjProp $ filterChL objectPropList e
       dp = map getIRI $ filterChL dataPropList e
   in PlainAxiom (ClassEntity ce) $ AnnFrameBit as $ ClassHasKey op dp

getOPAxiom :: Element -> Axiom
getOPAxiom e =
   let as = concatMap getAllAnnos $ elChildren e
       op = getObjProp $ fromJust
            $ filterChildName (isSmthList objectPropList) e
   in case getName e of
    "SubObjectPropertyOf" ->
       let opchain = concatMap (map getObjProp) $ map elChildren
            $ filterCh "ObjectPropertyChain" e
       in if null opchain
             then let opl = map getObjProp $ filterChL objectPropList e
                  in PlainAxiom (ObjectEntity $ head opl)
                       $ ListFrameBit (Just SubPropertyOf) $ ObjectBit
                          [(as, last opl)]
             else PlainAxiom (ObjectEntity op) $ AnnFrameBit as
                    $ ObjectSubPropertyChain opchain
    "EquivalentObjectProperties" ->
       let opl = map getObjProp $ filterChL objectPropList e
       in PlainAxiom (Misc as) $ ListFrameBit (Just (EDRelation Equivalent))
        $ ObjectBit $ map (\ x -> ([], x)) opl
    "DisjointObjectProperties" ->
       let opl = map getObjProp $ filterChL objectPropList e
       in PlainAxiom (Misc as) $ ListFrameBit (Just (EDRelation Disjoint))
        $ ObjectBit $ map (\ x -> ([], x)) opl
    "ObjectPropertyDomain" ->
       let ce = getClassExpression $ fromJust
            $ filterChildName (isSmthList classExpressionList) e
       in PlainAxiom (ObjectEntity op) $ ListFrameBit
          (Just (DRRelation ADomain)) $ ExpressionBit [(as, ce)]
    "ObjectPropertyRange" ->
       let ce = getClassExpression $ fromJust
            $ filterChildName (isSmthList classExpressionList) e
       in PlainAxiom (ObjectEntity op) $ ListFrameBit
          (Just (DRRelation ARange)) $ ExpressionBit [(as, ce)]
    "InverseObjectProperties" ->
       let opl = map getObjProp $ filterChL objectPropList e
       in PlainAxiom (ObjectEntity $ head opl)
                       $ ListFrameBit (Just InverseOf) $ ObjectBit
                          [(as, last opl)]
    "FunctionalObjectProperty" -> PlainAxiom (ObjectEntity op) $ ListFrameBit
        Nothing $ ObjectCharacteristics [(as, Functional)]
    "InverseFunctionalObjectProperty" -> PlainAxiom (ObjectEntity op)
        $ ListFrameBit Nothing $ ObjectCharacteristics [(as, InverseFunctional)]
    "ReflexiveObjectProperty" -> PlainAxiom (ObjectEntity op) $ ListFrameBit
        Nothing $ ObjectCharacteristics [(as, Reflexive)]
    "IrreflexiveObjectProperty" -> PlainAxiom (ObjectEntity op) $ ListFrameBit
        Nothing $ ObjectCharacteristics [(as, Irreflexive)]
    "SymmetricObjectProperty" -> PlainAxiom (ObjectEntity op) $ ListFrameBit
        Nothing $ ObjectCharacteristics [(as, Symmetric)]
    "AsymmetricObjectProperty" -> PlainAxiom (ObjectEntity op) $ ListFrameBit
        Nothing $ ObjectCharacteristics [(as, Asymmetric)]
    "TransitiveObjectProperty" -> PlainAxiom (ObjectEntity op) $ ListFrameBit
        Nothing $ ObjectCharacteristics [(as, Transitive)]
    _ -> error "not object property axiom"

getDPAxiom :: Element -> Axiom
getDPAxiom e =
   let as = concatMap getAllAnnos $ elChildren e
   in case getName e of
    "SubDataPropertyOf" ->
        let dpl = map getIRI $ filterChL dataPropList e
        in PlainAxiom (SimpleEntity $ Entity DataProperty $ head dpl)
              $ ListFrameBit (Just SubPropertyOf) $ DataBit [(as, last dpl)]
    "EquivalentDataProperties" ->
        let dpl = map getIRI $ filterChL dataPropList e
        in PlainAxiom (Misc as) $ ListFrameBit (Just (EDRelation Equivalent))
          $ DataBit $ map (\ x -> ([], x)) dpl
    "DisjointDataProperties" ->
        let dpl = map getIRI $ filterChL dataPropList e
        in PlainAxiom (Misc as) $ ListFrameBit (Just (EDRelation Disjoint))
          $ DataBit $ map (\ x -> ([], x)) dpl
    "DataPropertyDomain" ->
        let dp = getIRI $ fromJust $ filterChildName (isSmthList dataPropList) e
            ce = getClassExpression $ fromJust
                  $ filterChildName (isSmthList classExpressionList) e
        in PlainAxiom (SimpleEntity $ Entity DataProperty dp)
            $ ListFrameBit (Just (DRRelation ADomain)) $ ExpressionBit [(as, ce)]
    "DataPropertyRange" -> 
        let dp = getIRI $ fromJust $ filterChildName (isSmthList dataPropList) e
            dr = getDataRange $ fromJust
                  $ filterChildName (isSmthList dataRangeList) e
        in PlainAxiom (SimpleEntity $ Entity DataProperty dp)
            $ ListFrameBit (Just (DRRelation ARange)) $ DataPropRange [(as, dr)]
    "FunctionalDataProperty" ->
        let dp = getIRI $ fromJust $ filterChildName (isSmthList dataPropList) e
        in PlainAxiom (SimpleEntity $ Entity DataProperty dp)
            $ AnnFrameBit as DataFunctional
    _ -> error "not data property axiom"

getDataAssertion :: Element -> Axiom
getDataAssertion e =
   let as = concatMap getAllAnnos $ elChildren e
       dp = getIRI $ fromJust
                  $ filterChildName (isSmthList dataPropList) e
       ind = getIRI $ fromJust
                  $ filterChildName (isSmthList individualList) e
       lit = getLiteral $ fromJust
                  $ filterChildName (isSmth "Literal") e
   in case getName e of
    "DataPropertyAssertion" ->
         PlainAxiom (SimpleEntity $ Entity NamedIndividual ind)
           $ ListFrameBit Nothing $ IndividualFacts
               [(as, DataPropertyFact Positive dp lit)]
    "NegativeDataPropertyAssertion" ->
         PlainAxiom (SimpleEntity $ Entity NamedIndividual ind)
           $ ListFrameBit Nothing $ IndividualFacts
               [(as, DataPropertyFact Negative dp lit)]
    _ -> error "not data assertion"

getObjectAssertion :: Element -> Axiom
getObjectAssertion e =
   let as = concatMap getAllAnnos $ elChildren e
       op = getObjProp $ fromJust
                  $ filterChildName (isSmthList objectPropList) e
       ind = map getIRI $ filterChL individualList e
   in case getName e of
    "ObjectPropertyAssertion" ->
        PlainAxiom (SimpleEntity $ Entity NamedIndividual $ head ind)
           $ ListFrameBit Nothing $ IndividualFacts
               [(as, ObjectPropertyFact Positive op (last ind))]
    "NegativeObjectPropertyAssertion" ->
        PlainAxiom (SimpleEntity $ Entity NamedIndividual $ head ind)
           $ ListFrameBit Nothing $ IndividualFacts
               [(as, ObjectPropertyFact Negative op (last ind))]
    _ -> error "not object assertion"

getIndividualAssertion :: Element -> Axiom
getIndividualAssertion e = 
   let as = concatMap getAllAnnos $ elChildren e
       ind = map getIRI $ filterChL individualList e
   in case getName e of
    "SameIndividual" ->
        PlainAxiom (Misc as) $ ListFrameBit (Just (SDRelation Same))
          $ IndividualSameOrDifferent $ map (\ x -> ([], x)) ind
    "DifferentIndividuals" ->
        PlainAxiom (Misc as) $ ListFrameBit (Just (SDRelation Different))
          $ IndividualSameOrDifferent $ map (\ x -> ([], x)) ind
    _ -> error "not individual assertion"

getClassAssertion :: Element -> Axiom
getClassAssertion e = case getName e of
    "ClassAssertion" ->
        let as = concatMap getAllAnnos $ elChildren e
            ce = getClassExpression $ fromJust
                  $ filterChildName (isSmthList classExpressionList) e
            ind = getIRI $ fromJust
                  $ filterChildName (isSmthList individualList) e
        in PlainAxiom (SimpleEntity $ Entity NamedIndividual ind)
           $ ListFrameBit (Just Types) $ ExpressionBit [(as, ce)]
    _ -> error "not class assertion"

















