{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2004-2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(instances for URIreference and Namespace)

Pretty printing for OWL DL theories from abstract syntax to RDF\/OWL file.
-}

module OWL.PrintRDF where

import Common.Doc
import Text.XML.HXT.DOM.QualifiedName (QName(..))
import OWL.Sign
import OWL.AS

import qualified Common.AS_Annotation as AS_Anno
import qualified Data.Map as Map

-- import Debug.Trace

type AssMap = Map.Map IndividualURI OwlClassURI

class PrettyRDF a where
    printRDF  :: AssMap -> a -> Doc
--    printRDFs :: [a] -> AssMap -> Doc
--    printRDFs = brackets . ppWithCommas


instance PrettyRDF Sign where
    printRDF _ = printOntologyHead

printOntologyHead :: Sign -> Doc
printOntologyHead sig =
    let ns = namespaceMap sig
        oID = ontologyID sig
    in  text "<?xml version=\"1.0\"?>" $++$
         printNamespace oID ns     $++$ nest 4 <>
         text "<owl:Ontology" <+> printURI oID <> text ">" $+$ nest 4 <>
         text "</owl:Ontology>"

{-
<?xml version="1.0"?>

<!DOCTYPE rdf:RDF [
    <!ENTITY family "http://www.example.org/family#" >
    <!ENTITY owl "http://www.w3.org/2002/07/owl#" >
    <!ENTITY owl11 "http://www.w3.org/2006/12/owl11#" >
    <!ENTITY xsd "http://www.w3.org/2001/XMLSchema#" >
    <!ENTITY owl11xml "http://www.w3.org/2006/12/owl11-xml#" >
    <!ENTITY rdfs "http://www.w3.org/2000/01/rdf-schema#" >
    <!ENTITY rdf "http://www.w3.org/1999/02/22-rdf-syntax-ns#" >
]>

<rdf:RDF xmlns="http://www.example.org/family#"
     xml:base="http://www.example.org/family"
     xmlns:rdfs="http://www.w3.org/2000/01/rdf-schema#"
     xmlns:owl11="http://www.w3.org/2006/12/owl11#"
     xmlns:owl11xml="http://www.w3.org/2006/12/owl11-xml#"
     xmlns:family="http://www.example.org/family#"
     xmlns:owl="http://www.w3.org/2002/07/owl#"
     xmlns:xsd="http://www.w3.org/2001/XMLSchema#"
     xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#">
    <owl:Ontology rdf:about="">
        <rdfs:comment
            >An example to test features from OWL 1.1</rdfs:comment>
    </owl:Ontology>
-}


instance PrettyRDF URIreference where
    printRDF _ = printURI

printURI :: URIreference -> Doc
printURI ur =
    printURIWithAttr "rdf:about" ur

printResource :: URIreference -> Doc
printResource ur =
    printURIWithAttr "rdf:resource" ur

printURIWithAttr :: String -> URIreference -> Doc
printURIWithAttr attr (QN prefix localpart u)
  --  | localpart == "_" = text $ show "_"
    | null prefix = if null u then
                        text (attr ++ "=" ++ show localpart)
                      else if null localpart then
                               text (attr ++ "=" ++ show u)
                            else text (attr ++ "=" ++
                                       show (u ++ ";" ++ localpart))
    | otherwise = text (attr ++ "=" ++
                        show ("&" ++ prefix ++ ";" ++ localpart))

printNamespace :: OntologyID -> Namespace -> Doc
printNamespace oid nsMap =
  printDOCTYPE $++$
  text "<rdf:RDF" <+>
    text ("xmlns"++"=") <>
          text ("\"" ++ (localPart oid) ++ "#\"") $+$ nest 9 <>
    pp ("base", localPart oid) $+$ nest 9 <>
    (vcat $ map pp (Map.toList nsMap)) <+>
  text ">"
       where pp :: (String, String) -> Doc
             pp (s1,s2) = text ("xmlns:"++s1++"=") <> text ("\"" ++s2 ++ "\"")

             printDOCTYPE =
                 text "<!DOCTYPE rdf:RDF [" $+$ nest 4 <>
                    (vcat $ map printDT (Map.toList nsMap)) $+$
                 text "]>"
             printDT :: (String, String) -> Doc
             printDT (prefix, u) =
                 text ("<!ENTITY " ++ prefix ++ " \"" ++ u ++ "\">")

instance PrettyRDF SignAxiom where
    printRDF _ = text . show     -- printSignAxiom ignored

instance PrettyRDF Description where
    printRDF _ = printDescription

printDescription :: Description -> Doc
printDescription desc =
  case desc of
    OWLClass ocUri ->
        oneLineTagToDoc "rdf:Description" (printURI ocUri)
    -- text "<owl:Class" <+> printURI ocUri
    -- <+> text "/>"
    ObjectUnionOf descList ->        -- no example
        tagToDocWithAttr "owl:UnionOf" "rdf:parseType=\"Collection\""
          (listToDoc' (printRDF Map.empty) descList)

    ObjectIntersectionOf descList ->
        tagToDocWithAttr "owl:intersectionOf" "rdf:parseType=\"Collection\""
           (listToDoc' (printRDF Map.empty) descList)
     {-
      <owl:intersectionOf rdf:parseType="Collection">
        ...
        <rdf:Description rdf:about="#Person"/>
      </owl:intersectionOf>
     -}
    ObjectComplementOf d ->
        case d of
          OWLClass curi ->
              tagToDoc "owl:Class"
               (oneLineTagToDoc "owl:complementOf"
                                    (printResource curi))
          _ ->
              tagToDoc "owl:complementOf" (printRDF Map.empty d)

    ObjectOneOf indUriList ->
        tagToDocWithAttr "owl:oneOf" "rdf:parseType=\"Collection\""
          (listToDoc' (\i -> oneLineTagToDoc "rdf:Description" (printURI i))
                      indUriList)
    {-
      <owl:oneOf rdf:parseType="Collection">
         <rdf:Description rdf:about="#grandmother"/>
         <rdf:Description rdf:about="#mother"/>
         <rdf:Description rdf:about="#father"/>
         <rdf:Description rdf:about="#uncle"/>
         <rdf:Description rdf:about="#daughter"/>
         <rdf:Description rdf:about="#grandfather"/>
         <rdf:Description rdf:about="#son"/>
       </owl:oneOf>
     -}
    ObjectAllValuesFrom opExp d ->
        tagToDoc "owl:Restriction"
               (printOPERes opExp $+$
                tagToDoc "owl:allValuesFrom" (printRDF Map.empty d))
    {-
      <owl:Restriction>
         <owl:onProperty rdf:resource="#isMarriedTo"/>
         <owl:allValuesFrom rdf:resource="#Male"/>
      </owl:Restriction>
     -}

    ObjectSomeValuesFrom opExp d ->
        tagToDoc "owl:Restriction"
            (printOPERes opExp $+$
             tagToDoc "owl:someValuesFrom" (printRDF Map.empty d))

    ObjectExistsSelf opExp ->
        tagToDoc "owl11:SelfRestriction"
            (tagToDoc "owl:onProperty" (printRDF Map.empty opExp))

    ObjectHasValue opExp indUri ->
        tagToDoc "owl:Restriction"
            (printOPERes opExp $+$
             oneLineTagToDoc "owl:hasValue" (printResource indUri))

    ObjectMinCardinality card opExp maybeDesc ->
        tagToDoc "owl:Restriction"
         (text "<owl:minCardinality rdf:datatype=\"&xsd;nonNegativeInteger\">" <> text (show card) <> text "</owl:minCardinality>" $+$
          printOPERes opExp $+$
          maybe empty printOnClass maybeDesc)

    {-
      <owl:Restriction>
         <owl:onProperty rdf:resource="#hasChild"/>
         <owl11:onClass rdf:resource="#Female"/>
         <owl:minCardinality rdf:datatype="&xsd;nonNegativeInteger">2</owl:minCardinality>
      </owl:Restriction>
     -}

    ObjectMaxCardinality card opExp maybeDesc ->
        tagToDoc "owl:Restriction"
         (text "<owl:maxCardinality rdf:datatype=\"&xsd;nonNegativeInteger\">" <> text (show card) <> text "</owl:maxCardinality>" $+$
          printOPERes opExp $+$
          maybe empty printOnClass maybeDesc
         )

    ObjectExactCardinality card opExp maybeDesc ->
        tagToDoc "owl:Restriction"
         (text "<owl:cardinality rdf:datatype=\"&xsd;nonNegativeInteger\">" <> text (show card) <> text "</owl:cardinality>" $+$
          printOPERes opExp $+$
          maybe empty printOnClass maybeDesc)


    DataAllValuesFrom dpExp dpExpList dRange ->
        tagToDoc "owl:Restriction"
           (listToDoc' (\d -> oneLineTagToDoc "owl:onProperty"
                              (printResource d)) (dpExp:dpExpList) $+$
            tagToDoc "owl:allValuesFrom" (tagToDoc "rdf:Description"
                            (printRDF Map.empty  dRange)))
    {-
       <owl:Restriction>
          <owl:onProperty rdf:resource="#hasAge"/>
          <owl:allValuesFrom>
             ..  ..
          </owl:allValuesFrom>
       </owl:Restriction>
     -}
    DataSomeValuesFrom  dpExp dpExpList dRange ->
        tagToDoc "owl:Restriction"
           (listToDoc' (\d -> oneLineTagToDoc "owl:onProperty"
                              (printResource d)) (dpExp:dpExpList) $+$
            tagToDoc "owl:someValuesFrom" (printRDF Map.empty  dRange))

    DataHasValue dpExp cons ->
        tagToDoc "owl:Restriction"
           (oneLineTagToDoc "owl:onProperty" (printResource dpExp)$+$
            tagToDoc "owl:hasValue" (printRDF Map.empty  cons))

    DataMinCardinality card dpExp maybeRange ->
        tagToDoc "owl:Restriction"
           (oneLineTagToDoc "owl:onProperty" (printResource dpExp) $+$
            text "<owl:minCardinality rdf:datatype=\"&xsd;nonNegativeInteger\">" <> text (show card)  <> text "</owl:minCardinality>" $+$
            maybe empty (printRDF Map.empty) maybeRange)

    DataMaxCardinality  card dpExp maybeRange ->
        tagToDoc "owl:Restriction"
           (oneLineTagToDoc "owl:onProperty" (printResource dpExp) $+$
            text "<owl:maxCardinality rdf:datatype=\"&xsd;nonNegativeInteger\">" <> text (show card) <> text "</owl:maxCardinality>" $+$
            maybe empty (printRDF Map.empty) maybeRange)

    DataExactCardinality  card dpExp maybeRange ->
        tagToDoc "owl:Restriction"
           (oneLineTagToDoc "owl:onProperty" (printResource dpExp) $+$
            text "<owl:cardinality rdf:datatype=\"&xsd;nonNegativeInteger\">" <> text (show card) <> text "</owl:cardinality>" $+$
            maybe empty (printRDF Map.empty) maybeRange)


instance PrettyRDF ObjectPropertyExpression where
    printRDF _ = printObjPropExp

printObjPropExp :: ObjectPropertyExpression -> Doc
printObjPropExp opExp =
    case opExp of
     OpURI ou -> oneLineTagToDoc "owl:ObjectProperty"  (printURI ou)
     InverseOp iopExp -> tagToDoc "owl:InverseObjectProperties"
                            (printRDF Map.empty iopExp)
    {-
      <owl:ObjectProperty rdf:about="#hasChild">
          <owl:inverseOf rdf:resource="#hasParent"/>
      </owl:ObjectProperty>
     -}

printOPERes :: ObjectPropertyExpression -> Doc
printOPERes opExp =
    case opExp of
     OpURI ou -> oneLineTagToDoc "owl:onProperty"  (printResource ou)
     InverseOp iopExp -> tagToDoc "owl:InverseObjectProperties"
                            (printOPERes iopExp)


printURIFromOPExp :: ObjectPropertyExpression -> Doc
printURIFromOPExp opExp =
    case opExp of
      OpURI ou -> printURI ou
      _ -> error ("ObjectPropertyExpression has not only the URI: "
                   ++ show opExp)

printURIFromOPExpRes :: ObjectPropertyExpression -> Doc
printURIFromOPExpRes opExp =
    case opExp of
      OpURI ou -> printResource ou
      _ -> error ("ObjectPropertyExpression has not only the URI: "
                   ++ show opExp)

printURIFromDesc :: Description -> Doc
printURIFromDesc desc =
    case desc of
      OWLClass curi -> printURI curi
      _  -> error ("Description has not only a class URI:" ++ show desc)

printURIFromDescRes :: Description -> Doc
printURIFromDescRes desc =
    case desc of
      OWLClass curi -> printResource curi
      _  -> error ("Description has not only a class: " ++ show desc)


instance PrettyRDF DataRange where
    printRDF _ = printDataRange

{-
  <owl:DatatypeProperty rdf:ID="datatypeProperty_1">
    <rdfs:range>
      <owl:DataRange>
        <owl:oneOf rdf:parseType="Resource">
          <rdf:rest
rdf:resource="http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"/>
          <rdf:first
rdf:datatype="http://www.w3.org/2001/XMLSchema#string"
          >78</rdf:first>
        </owl:oneOf>
      </owl:DataRange>
    </rdfs:range>
  </owl:DatatypeProperty>
-}

printDataRange :: DataRange -> Doc
printDataRange dr =
  --  (tagToDoc "owl:DataRange"
   case dr of
     DRDatatype du ->
        oneLineTagToDoc "rdf:datatype"
                                 (printResource du)
         --  <Datatype URI="&rdfs;Literal"/>
     DataComplementOf drange ->
        tagToDoc "owl:ComplementOf"
            (tagToDoc "rdf:Description" $ printRDF Map.empty drange)
     DataOneOf constList ->
        text "<owl:oneOf rdf:parseType=\"Resource\">" $+$nest 4 <>
          listToDoc' (printRDF Map.empty) constList $+$
        text "</owl:oneOf>"
     DatatypeRestriction drange l ->
        -- DatatypeRestriction DataRange [(DatatypeFacet, RestrictionValue)]
        oneLineTagToDoc "rdf:type" (text "rdf:resource=\"&owl;DataRange\"")
         $+$ oneLineTagToDoc "owl11:onDataRange"
                 (case drange of
                    DRDatatype u -> printResource u
                    _ -> error "unknown datatype.")
         $+$ (vcat $ map printFV l)

printOnClass :: Description -> Doc
printOnClass desc =
    case desc of
      OWLClass c -> oneLineTagToDoc "owl11:onClass" (printResource c)
      _ -> text $ show desc   -- debug
    -- <owl11:onClass rdf:resource="#Female"/>


printFV :: (DatatypeFacet, RestrictionValue) -> Doc
printFV (facet, restValue) = printFacet facet
                                    (getValueFromConst restValue)

getValueFromConst :: Constant -> Doc
getValueFromConst cons =
    case cons of
      TypedConstant (lexi, _) ->
          text lexi
      UntypedConstant (lexi, _) ->
          text lexi

printFacet :: DatatypeFacet -> Doc -> Doc
printFacet facet doc =
    (text "<" <> printRDF  Map.empty facet <+> text "rdf:datatype=\"&xsd;int\">") <>
      doc <>
    text "</"<> printRDF  Map.empty facet <> text ">"

instance PrettyRDF DatatypeFacet where
    printRDF _ df =
        case df of
          LENGTH -> text "owl11:length"
          MINLENGTH -> text "owl11:minLength"
          MAXLENGTH -> text "owl11:maxLength"
          PATTERN -> text "owl11:pattern"
          MININCLUSIVE -> text "owl11:minInclusive"
          MINEXCLUSIVE -> text "owl11:minExclusive"
          MAXINCLUSIVE -> text "owl11:maxInclusive"
          MAXEXCLUSIVE -> text "owl11:maxExclusive"
          TOTALDIGITS -> text "owl11:totalDigits"
          FRACTIONDIGITS -> text "owl11:fractionDigits"

instance PrettyRDF Constant where
    printRDF _ cons =
        case cons of
          TypedConstant (lexi, u) ->
              text "<owl11:Constant rdfs:Datatype=" <>
                       (text $ show$localPart u) <>
                   text (">" ++ lexi) <> text "</owl11:Constant>"
   -- <Constant Datatype="&xsd;int">20</Constant>
          UntypedConstant (lexi, _) ->
              text "<owl11:Constant>" <>
                   (text $ lexi) <> (text "</owl11:Constant>")


instance PrettyRDF Entity where
    printRDF _ = printEntity

printEntity :: Entity -> Doc
printEntity entity =
    case entity of
       Datatype dUri ->
           oneLineTagToDoc "rdfs:Datatype" (printURI dUri)
       OWLClassEntity cUri ->
           oneLineTagToDoc "owl:OWLClass" (printURI cUri)
       ObjectProperty opUri ->
           oneLineTagToDoc "owl:ObjectProperty" (printURI opUri)
       DataProperty dpUri ->
           oneLineTagToDoc "owl:DatatypeProperty" (printURI dpUri)
       Individual iUri ->
           oneLineTagToDoc "owl11:Individual" (printURI iUri)

instance PrettyRDF Sentence where
    printRDF = printSentence

printSentence :: AssMap -> Sentence -> Doc
printSentence m sent = case sent of
    OWLAxiom axiom -> nest 4 <> printRDF m axiom
    OWLFact fact   -> nest 4 <> printRDF m fact

instance PrettyRDF Axiom where
    printRDF = printAxiom

printAxiom :: AssMap -> Axiom -> Doc
printAxiom indClsMap axiom = case axiom of
   SubClassOf _ sub super ->
       tagToDocWithAttr' "owl:Class" (printURIFromDesc sub)
         (tagToDoc "rdfs:subClassOf" (printRDF Map.empty  super))
   {-
    <owl:Class rdf:about="#Male">
        <rdfs:subClassOf>
            <owl:Restriction>
                <owl:onProperty rdf:resource="#isMarriedTo"/>
                <owl:allValuesFrom rdf:resource="#Female"/>
            </owl:Restriction>
        </rdfs:subClassOf>
    </owl:Class>
    -}

   EquivalentClasses _ (clazz:equiList) ->
       printClass clazz
          (equivalentClassTag
             $ listToDoc' (\d -> case d of
                                  ObjectIntersectionOf _ -> tagToDoc "owl:Class" (printRDF Map.empty  d)
                                  ObjectOneOf _ ->  tagToDoc "owl:Class" (printRDF Map.empty  d)
                                  _ -> printRDF  Map.empty d) equiList)
   {-
    <owl:Class rdf:about="#Adult">
        <owl:equivalentClass>
            <owl:Class>
                <owl:intersectionOf rdf:parseType="Collection">
                    <owl:Restriction>
                        <owl:onProperty rdf:resource="#hasAge"/>
                        <owl:allValuesFrom>
                            <rdf:Description>
                                <rdf:type rdf:resource="&owl;DataRange"/>
                                <owl11:minInclusive rdf:datatype="&xsd;int">20</owl11:minInclusive>
                                <owl11:onDataRange rdf:resource="&xsd;nonNegativeInteger"/>
                            </rdf:Description>
                        </owl:allValuesFrom>
                    </owl:Restriction>
                    <rdf:Description rdf:about="#Person"/>
                </owl:intersectionOf>
            </owl:Class>
        </owl:equivalentClass>
        <owl:equivalentClass rdf:resource="#Child"/>
    </owl:Class>
   -}

   DisjointClasses _ (clazz:djList) ->
       tagToDocWithAttr' "owl:Class" (printURIFromDesc clazz)
         (tagToDoc "owl:disjointWith" (listToDoc' (printRDF Map.empty) djList))
    {-
     <owl:Class rdf:about="#Teenager">
         <owl:disjointWith rdf:resource="#Adult"/>
     </owl:Class>
    -}

   DisjointUnion _ curi discList ->
       tagToDocWithAttr' "owl:Class" (printURI curi)
         (tagToDocWithAttr "owl11:disjointUnionOf" "rdf:parseType=\"Collection\"" (listToDoc' (printRDF Map.empty) discList))
   {-
     <owl:Class rdf:about="#Person">
        <owl11:disjointUnionOf rdf:parseType="Collection">
            <rdf:Description rdf:about="#Female"/>
            <rdf:Description rdf:about="#Male"/>
        </owl11:disjointUnionOf>
     </owl:Class>
    -}

   -- ObjectPropertyAxiom
   SubObjectPropertyOf _ sopExp opExp ->
     case sopExp of
       OPExpression oexp ->
        tagToDocWithAttr' "owl:ObjectProperty" (printURIFromOPExp oexp)
           (tagToDoc "rdfs:subPropertyOf" (printRDF Map.empty  opExp))
       SubObjectPropertyChain oeList ->
           tagToDoc "rdf:Description"
             (listToDoc (printRDF Map.empty) oeList $+$
              oneLineTagToDoc "rdfs:subPropertyOf"
                                  (printURIFromOPExpRes opExp))

    {-1.
     <owl:ObjectProperty rdf:about="#dislikes">
        <rdfs:subPropertyOf rdf:resource="#hasChild"/>
        <owl11:disjointObjectProperties rdf:resource="#likes"/>
     </owl:ObjectProperty>
      2.
    <rdf:Description>
        <rdf:type rdf:resource="&rdf;List"/>
        <rdf:first rdf:resource="#hasAncestor"/>
        <rdfs:subPropertyOf rdf:resource="#hasAncestor"/>
        <rdf:rest rdf:parseType="Collection">
            <rdf:Description rdf:about="#hasAncestor"/>
        </rdf:rest>
    </rdf:Description>
    -}

   EquivalentObjectProperties _ (opExp:opList) ->
       tagToDocWithAttr' "owl:ObjectProperty" (printURIFromOPExp opExp)
           (listToDoc' (\o -> oneLineTagToDoc "owl:equivalentProperty"
                          (printURIFromOPExpRes o)) opList)
    {-
      <owl:ObjectProperty rdf:about="#hasSon">
        <rdfs:range rdf:resource="#Male"/>
        <owl:equivalentProperty rdf:resource="#hasSibling"/>
        <rdfs:subPropertyOf rdf:resource="#hasChild"/>
        <owl:equivalentProperty rdf:resource="#hasDaughter"/>
      </owl:ObjectProperty>
    -}

   DisjointObjectProperties _ (opExp:opList) ->
        tagToDocWithAttr' "owl:ObjectProperty" (printURIFromOPExp opExp)
           (listToDoc' (\o -> oneLineTagToDoc "owl11:disjointObjectProperties"
                          (printURIFromOPExpRes o)) opList)

   ObjectPropertyDomain _ opExp desc ->
       tagToDocWithAttr' "owl:ObjectProperty"
                             (printURIFromOPExp opExp)
          (case desc of
             OWLClass _ -> oneLineTagToDoc "rdfs:domain"
                               (printURIFromDescRes desc)
             _ -> tagToDoc "rdfs:domain"
                        (printRDF Map.empty desc))
    {-
      <owl:ObjectProperty rdf:about="#hasAncestor">
        <rdfs:domain rdf:resource="#Person"/>
        <rdfs:range rdf:resource="#Person"/>
      </owl:ObjectProperty>
    -}
   ObjectPropertyRange  _ opExp desc ->
       tagToDocWithAttr' "owl:ObjectProperty" (printURIFromOPExp opExp)
          (oneLineTagToDoc "rdfs:range" (printURIFromDescRes desc))

   InverseObjectProperties  _ opExp1 opExp2 ->
       tagToDocWithAttr' "owl:ObjectProperty"
                             (printURIFromOPExp opExp1)
          (oneLineTagToDoc "owl:inverseOf" (printURIFromOPExpRes opExp2))
    {-
      <owl:ObjectProperty rdf:about="#hasBrother">
        <owl:inverseOf rdf:resource="#hasSister"/>
      </owl:ObjectProperty>
    -}
   FunctionalObjectProperty _ opExp ->
      tagToDocWithAttr' "owl:ObjectProperty" (printURIFromOPExp opExp)
        (text "<rdf:type rdf:resource=\"&owl;FunctionalProperty\"/>")
    {-
      <owl:ObjectProperty rdf:about="#hasFather">
        <rdf:type rdf:resource="&owl;FunctionalProperty"/>
        <rdf:type rdf:resource="&owl11;AntisymmetricProperty"/>
        <rdf:type rdf:resource="&owl;InverseFunctionalProperty"/>
        <rdf:type rdf:resource="&owl11;ReflexiveProperty"/>
        <rdf:type rdf:resource="&owl11;IrreflexiveProperty"/>
        <rdf:type rdf:resource="&owl;TransitiveProperty"/>
        <rdf:type rdf:resource="&owl;SymmetricProperty"/>
        <rdfs:subPropertyOf rdf:resource="#hasParent"/>
        <rdfs:range rdf:resource="#Male"/>
      </owl:ObjectProperty>
    -}
   InverseFunctionalObjectProperty _ opExp ->
      tagToDocWithAttr' "owl:ObjectProperty" (printURIFromOPExp opExp)
        (text "<rdf:type rdf:resource=\"&owl;InverseFunctionalProperty\"/>")

   ReflexiveObjectProperty  _ opExp ->
      tagToDocWithAttr' "owl:ObjectProperty" (printURIFromOPExp opExp)
        (text "<rdf:type rdf:resource=\"&owl11;ReflexiveProperty\"/>")

   IrreflexiveObjectProperty  _ opExp ->
      tagToDocWithAttr' "owl:ObjectProperty" (printURIFromOPExp opExp)
        (text "<rdf:type rdf:resource=\"&owl11;IrreflexiveProperty\"/>")
   SymmetricObjectProperty  _ opExp ->
      tagToDocWithAttr' "owl:ObjectProperty" (printURIFromOPExp opExp)
        (text "<rdf:type rdf:resource=\"&owl;SymmetricProperty\"/>")
   AntisymmetricObjectProperty  _ opExp ->
      tagToDocWithAttr' "owl:ObjectProperty" (printURIFromOPExp opExp)
        (text "<rdf:type rdf:resource=\"&owl;AntisymmetricProperty\"/>")
   TransitiveObjectProperty _ opExp ->
      tagToDocWithAttr' "owl:ObjectProperty" (printURIFromOPExp opExp)
        (text "<rdf:type rdf:resource=\"&owl;TransitiveProperty\"/>")

   -- DataPropertyAxiom
       -- no example
   SubDataPropertyOf _ dpExp1 dpExp2 ->
     tagToDocWithAttr' "owl:DatatypeProperty" (printURI dpExp1)
        (oneLineTagToDoc "rdfs:subPropertyOf" (printResource dpExp2))
    {-
      <owl:DatatypeProperty rdf:about="#isOfAge">
        <rdf:type rdf:resource="&owl;FunctionalProperty"/>
        <rdfs:range rdf:resource="&xsd;integer"/>
        <owl:equivalentProperty rdf:resource="#topDataProperty"/>
        <owl11:disjointDataProperties rdf:resource="#hasAge"/>
        <rdfs:subPropertyOf rdf:resource="#topDataProperty"/>
      </owl:DatatypeProperty>
     -}
   EquivalentDataProperties  _ (dpExp:dpList) ->
     tagToDocWithAttr' "owl:DatatypeProperty" (printURI dpExp)
        (listToDoc' (\dp -> oneLineTagToDoc "owl:equivalentProperty"
                              (printResource dp)) dpList)

   DisjointDataProperties  _ (dpExp:dpList) ->
     tagToDocWithAttr' "owl:DatatypeProperty" (printURI dpExp)
        (listToDoc' (\dp -> oneLineTagToDoc "owl11:disjointDataProperties"
                              (printResource dp)) dpList)

   DataPropertyDomain  _ dpExp desc ->
       tagToDocWithAttr' "owl:DatatypeProperty" (printURI dpExp)
          (tagToDoc "rdfs:domain" (printRDF Map.empty  desc))
    {-
      <owl:DatatypeProperty rdf:about="#testDataProperty1">
        <rdfs:domain rdf:resource="#Female"/>
      </owl:DatatypeProperty>
     -}
   DataPropertyRange  _ dpExp drange ->
       tagToDocWithAttr' "owl:DatatypeProperty" (printURI dpExp)
        (case drange of
           DRDatatype did ->
             oneLineTagToDoc "rdfs:range" (printResource did)
           _ ->
             (tagToDoc "rdfs:range" (printRDF Map.empty drange)))

   FunctionalDataProperty _ dpExp ->
      tagToDocWithAttr' "owl:DatatypeProperty" (printURI dpExp)
        (text "<rdf:type rdf:resource=\"&owl;FunctionalProperty\"/>")

   -- Fact
   -- see http://www.w3.org/2007/OWL/draft/ED-owl11-xml-serialization-20080326/#The_XML_Schema
   SameIndividual _ (ind:indList) ->
       case Map.lookup ind indClsMap of
         Just classId ->
             let clz = classNameForInd classId
             in tagToDocWithAttr' clz (printURI ind)
                    (listToDoc'
                     (\i -> oneLineTagToDoc "owl:sameAs"
                            (printResource i)) indList)
         Nothing ->
             tagToDoc "owl11:SameIndividual"
                          ((printIndividual ind)
                           $+$ (listToDoc printIndividual indList))
    {-
      <Person rdf:about="#personX">
        <owl:sameAs rdf:resource="#uncle"/>
        <owl:sameAs rdf:resource="#father"/>
      </Person>
     -}

   DifferentIndividuals _ (ind:indList) ->
       tagToDoc "rdf:Description"
         (text "<rdf:type rdf:resource=\"&owl;AllDifferent\"/>" $+$
          tagToDocWithAttr "owl:distinctMembers" "rdf:parseType=\"Collection\"" (listToDoc' (\d -> oneLineTagToDoc "rdf:Description" (printURI d)) (ind:indList)))
    {-
      <rdf:Description>
        <rdf:type rdf:resource="&owl;AllDifferent"/>
        <owl:distinctMembers rdf:parseType="Collection">
            <rdf:Description rdf:about="#personY"/>
            <rdf:Description rdf:about="#father"/>
        </owl:distinctMembers>
      </rdf:Description>
     -}
   ClassAssertion _ ind desc ->
     case Map.lookup ind  indClsMap of
       Just clsOfInd ->
           case desc of
             OWLClass curi ->
                 -- if the classAssertion is only a declaration of
                 -- individual, a oneline-tag is used oder ignored.
                 if clsOfInd == curi then
                    -- oneLineTagToDoc (localPart curi)
                    --                 (printURI ind)
                     empty
                   else printClassAssertion clsOfInd ind desc
             _ -> printClassAssertion clsOfInd ind desc
       Nothing ->
           tagToDoc "owl11:ClassAssertion"
                ((case desc of
                    OWLClass ouri ->
                      text "<owl:Class" <+> printResource ouri
                                        <+> text "/>"
                    _ -> printRDF Map.empty  desc)
                 $+$ printIndividual ind)
   {-
     <Person rdf:about="#father">
        <rdf:type>
            <owl:Restriction>
                <owl:onProperty rdf:resource="#hasChild"/>
                <owl:allValuesFrom rdf:resource="#FamilyMembers"/>
            </owl:Restriction>
        </rdf:type>
     </Person>
    -}

   ObjectPropertyAssertion _ opExp source target ->
       case Map.lookup source indClsMap of
         Just curi ->
             tagToDocWithAttr' (classNameForInd curi) (printURI source)
               (case opExp of
                  OpURI ou -> oneLineTagToDoc (classNameForInd ou)
                                 (printResource target)
                  InverseOp _ ->  -- on idee, error?
                       error ("ObjectPropertyAssertion can not accept a inverse object property expression.")
               )
         Nothing ->  -- without classAssertion of source the object-
                     -- propertyAssertion can't be declared in RDF.
             tagToDoc "owl11:ObjectPropertyAssertion"
                (printOPERes opExp $+$ printIndividual source
                 $+$ printIndividual target)
  {-
    <ObjectPropertyAssertion>
        <ObjectProperty URI="&family;hasMother"/>
        <Individual URI="&family;father"/>
        <Individual URI="&family;grandmother"/>
    </ObjectPropertyAssertion>
   ---------------->>
    <Person rdf:about="#father">
        <hasMother rdf:resource="#grandmother"/>
    </Person>
   -}

   NegativeObjectPropertyAssertion  _ opExp source target ->
       tagToDoc "owl11:NegativeObjectPropertyAssertion"
          (printSubject source <+>
           printPredicate opExp <+>
           printObject target)
   {-
    <owl11:NegativeObjectPropertyAssertion>
        <rdf:subject rdf:resource="#father"/>
        <rdf:predicate rdf:resource="#hasBrother"/>
        <rdf:object rdf:resource="#uncle"/>
    </owl11:NegativeObjectPropertyAssertion>
    -}

   DataPropertyAssertion  _ dpExp source target ->
       case Map.lookup source indClsMap of
         Just curi ->
             tagToDocWithAttr' (classNameForInd curi) (printURI source)
                  (printDPWithConst dpExp target)
         Nothing ->
             tagToDoc "owl11:DataPropertyAssertion"
                 (oneLineTagToDoc "owl11:DataProperty"
                        (printResource dpExp)
                  $+$ printIndividual source
                  $+$ printRDF Map.empty  target)
   {-
    <Person rdf:about="#father">
        <hasAge rdf:datatype="&xsd;int">38</hasAge>
    </Person>
   -}

   NegativeDataPropertyAssertion  _ dpExp source target ->
       tagToDoc "owl11:NegativeDataPropertyAssertion"
         (printSubject source
          $+$ printPredicateDataProp dpExp
          $+$ printObjectDataProp target
          )
    {-
    <owl11:NegativeDataPropertyAssertion>
        <rdf:subject rdf:resource="#father"/>
        <rdf:predicate rdf:resource="#hasName"/>
        <rdf:object rdf:datatype="&xsd;string">RRRRRRRRR</rdf:object>
    </owl11:NegativeDataPropertyAssertion>
   -}

   Declaration _ entity ->
     {-  case entity of ->
         Datatype u ->
         OWLClassEntity u
         ObjectProperty u
         DataProperty u
         Individual u
      -}
       tagToDoc "Declaration"
                (printRDF Map.empty  entity)
   EntityAnno _ -> empty    -- EntityAnnotation, here the "implied" comes
   u -> error ("unknow axiom" ++ show u)


instance PrettyRDF SubObjectPropertyExpression where
    printRDF _ sopExp =
        case sopExp of
          OPExpression opExp ->
              tagToDoc "rdfs:subPropertyOf" (printRDF Map.empty  opExp)

          SubObjectPropertyChain opExpList ->
              tagToDoc "rdfs:subPropertyOf"
                (tagToDoc "owl11:propertyChain"
                  (listToDoc' (printRDF Map.empty) opExpList))

    {-
      <owl:ObjectProperty rdf:about="#dislikes">
        <rdfs:subPropertyOf rdf:resource="#hasChild"/>
        <owl11:disjointObjectProperties rdf:resource="#likes"/>
      </owl:ObjectProperty>
     -}



printClass :: Description -> Doc -> Doc
printClass desc content =
    case desc of
      OWLClass curi ->
          classStart curi $+$
          nest 4 <>  content  $+$
          classEnd
      _ -> error ("Class here muss be a delaration of OWLClass")
  where
    classStart :: OwlClassURI  -> Doc
    classStart cu =
        text "<owl:Class" <+> printURI cu
                          <+> text ">"

    classEnd :: Doc
    classEnd = text "</owl:Class>"


equivalentClassTag :: Doc -> Doc
equivalentClassTag doc =
    text "<owl:equivalentClass>" $+$
      nest 4 <> doc $+$
    text "</owl:equivalentClass>"

classTag :: Description -> Doc -> Doc
classTag desc content =
    case desc of
      OWLClass curi ->
          classStart curi $+$
          nest 4 <>  content  $+$
          classEnd
      _ -> error ("Class here muss be a delaration of OWLClass")
  where
    classStart :: OwlClassURI  -> Doc
    classStart cu =
        text "<owl:Class" <+> printURI cu
                          <+> text ">"

    classEnd :: Doc
    classEnd = text "</owl:Class>"

classTag' :: OwlClassURI -> Doc -> Doc
classTag' curi d =
    classTag (OWLClass curi) d

printIndividual :: IndividualURI -> Doc
printIndividual iuri =
    oneLineTagToDoc "owl11:Individual" (printResource iuri)

printDataProperty :: DataPropertyExpression -> Doc
printDataProperty dpe =
    oneLineTagToDoc "owl11:DataProperty" (printRDF Map.empty  dpe)

printSubject :: SourceIndividualURI -> Doc
printSubject ind =
    oneLineTagToDoc "rdf:subject" (printResource ind)

printObject :: TargetIndividualURI -> Doc
printObject ind =
    oneLineTagToDoc "rdf:object" (printResource ind)

printPredicate :: ObjectPropertyExpression -> Doc
printPredicate ope =
    case ope of
       OpURI oUri -> oneLineTagToDoc "rdf:predicate"
                               (printResource oUri)
       InverseOp _ -> error ("NegativeObjectPropertyAssertion can not accept a inverse object property expression.")

printPredicateDataProp :: DataPropertyExpression -> Doc
printPredicateDataProp dpe =
    oneLineTagToDoc "rdf:predicate" (printResource dpe)

printObjectDataProp :: TargetValue -> Doc
printObjectDataProp cons =
   tagToDocWithAttr' "rdf:object"
      (case cons of
         TypedConstant (_, ty) ->
             printURIWithAttr "rdf:datatype" ty
         UntypedConstant _ -> empty)
      (getValueFromConst cons)

printDPWithConst :: DataPropertyExpression
                 -> Constant -> Doc
printDPWithConst dpe cons =
    tagToDocWithAttr' (localPart dpe)
      (case cons of
         TypedConstant (_, ty) ->
             printURIWithAttr "rdf:datatype" ty
         UntypedConstant _ -> empty)
      (getValueFromConst cons)

tagToDoc :: String -> Doc -> Doc
tagToDoc tag content =
    text ("<" ++ tag ++ ">") $+$
       nest 4 <> content  $+$
    text ("</" ++ tag ++ ">")

tagToDocWithAttr :: String -> String -> Doc -> Doc
tagToDocWithAttr tag attr content =
    text ("<" ++ tag ++ " " ++ attr ++ ">") $+$
       nest 4 <> content  $+$
    text ("</" ++ tag ++ ">")

tagToDocWithAttr' :: String -> Doc -> Doc -> Doc
tagToDocWithAttr' tag attr content =
    text ("<" ++ tag) <+> attr <> text ">" $+$
       nest 4 <> content  $+$
    text ("</" ++ tag ++ ">")

cardinalityToDoc :: String -> Cardinality -> Doc -> Doc
cardinalityToDoc tag card d =
    text ("<owl11:" ++ tag ++ " owl11:cardinality=\"" ++
                       show card ++ "\">") $+$
       nest 4 <> d  $+$
    text ("</owl11:" ++ tag ++ ">")

printClassAssertion :: OwlClassURI -> IndividualURI
                    -> Description -> Doc
printClassAssertion clsOfInd ind desc =
    tagToDocWithAttr' (classNameForInd clsOfInd) (printURI ind)
       (tagToDoc "rdf:type" (printRDF Map.empty  desc))
   {-
     <Person rdf:about="#father">
        <rdf:type>
            <owl:Restriction>
                <owl:onProperty rdf:resource="#hasChild"/>
                <owl:allValuesFrom rdf:resource="#FamilyMembers"/>
            </owl:Restriction>
        </rdf:type>
     </Person>
    -}

oneLineTagToDoc :: String -> Doc -> Doc
oneLineTagToDoc s content =
    text ("<" ++ s) <+> content <> text "/>"

-- not necessary
instance PrettyRDF OntologyFile where
    printRDF _ = text . show

instance PrettyRDF Ontology where
    printRDF _ = text . show  -- printOntology

instance PrettyRDF [AS_Anno.Named Sentence] where
    printRDF m l = foldl ($+$) empty $ map (printRDF m) l

instance PrettyRDF (AS_Anno.Named Sentence) where
    printRDF m s = printRDF m (AS_Anno.sentence s)


listToDoc :: (PrettyRDF a) =>
             (a -> Doc) -> [a] -> Doc
listToDoc pf list =
    text "<rdf:type rdf:resource=\"&rdf;List\"/>"
     $+$ (ltd pf list)
   where
     ltd _ [] = empty
     ltd p (lastOne:[]) =
      text ("<rdf:rest " ++
       "rdf:resource=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#nil\"/>")
        $+$ (tagToDoc "rdf:first" (p lastOne))
     ltd p (h:r) =
         text "<rdf:rest rdf:parseType=\"Resource\">" $+$
              nest 4 <> ltd p r $+$
                   text "</rdf:rest>" $+$
              (tagToDoc "rdf:first" (p h))

listToDoc' :: (PrettyRDF a) =>
              (a -> Doc) -> [a] -> Doc
listToDoc' p  = vcat . map p


classNameForInd ::OwlClassURI -> String
classNameForInd cid =
    let lp = localPart cid
    in if lp == "Thing" then
           "owl:" ++ lp
         else lp

emptyQN :: QName
emptyQN = QN "" "" ""

simpleQN :: String -> QName
simpleQN str = QN "" str ""

choiceName :: Int -> String
choiceName level
    | level <= 0 = "x"
    | level == 1 = "y"
    | level == 2 = "z"
    | otherwise = "u" ++ (show (level -2))

nest :: Int -> Doc
nest longOfNest
    | longOfNest == 0 = empty
    | otherwise = space <> (nest (longOfNest -1))
