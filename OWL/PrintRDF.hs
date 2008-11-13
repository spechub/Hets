{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2004-2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(instances for URIreference and Namespace)

Pretty printing for OWL DL theories from abstract syntax to RDF\/OWL file.
-}

module OWL.PrintRDF (printRDF) where

import Common.Doc

import OWL.Sign
import OWL.AS

import qualified Common.AS_Annotation as AS_Anno
import qualified Data.Map as Map

import Data.Char

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
                        text (attr ++ "=" ++ show ('#':localpart))
                      else if null localpart then
                               text (attr ++ "=" ++ show u)
                            else text (attr ++ "=" ++
                                       show (localpart))
    | otherwise = text (attr ++ "=" ++
                        show ("&" ++ prefix ++ ":" ++ localpart))

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

downCaseFirst :: String -> String
downCaseFirst s = case s of
 c : r -> toLower c : r
 _ -> error "PrintRDF.downCaseFirst"

junctionType :: JunctionType -> String
junctionType ty = "owl:" ++ downCaseFirst (show ty)


cardinalityType :: CardinalityType -> String
cardinalityType ty = "owl:" ++ case ty of
    ExactCardinality -> "cardinality"
    _ -> downCaseFirst (show ty)

cardinalityTag :: CardinalityType -> Int -> Doc
cardinalityTag ty c = let ct = cardinalityType ty in text $
  "<" ++ ct ++ " rdf:datatype=\"&xsd;nonNegativeInteger\">" ++ show c
   ++ "</" ++ ct ++ ">"

quantifierType :: QuantifierType -> String
quantifierType ty = "owl:" ++ downCaseFirst (show ty)

printDescription :: Description -> Doc
printDescription desc =
  case desc of
    OWLClass ocUri ->
        oneLineTagToDoc "rdf:Description" (printURI ocUri)
    -- text "<owl:Class" <+> printURI ocUri
    -- <+> text "/>"
    ObjectJunction ty descList ->        -- no example
        tagToDoc ("owl:Class") $
        tagToDocWithAttr (junctionType ty) "rdf:parseType=\"Collection\""
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
    ObjectValuesFrom ty opExp d ->
        tagToDoc "owl:Restriction"
               (printOPERes opExp $+$
                tagToDoc (quantifierType ty) (printRDF Map.empty d))
    {-
      <owl:Restriction>
         <owl:onProperty rdf:resource="#isMarriedTo"/>
         <owl:allValuesFrom rdf:resource="#Male"/>
      </owl:Restriction>
     -}
    ObjectExistsSelf opExp ->
        tagToDoc "owl:SelfRestriction"
            (tagToDoc "owl:onProperty" (printRDF Map.empty opExp))

    ObjectHasValue opExp indUri ->
        tagToDoc "owl:Restriction"
            (printOPERes opExp $+$
             oneLineTagToDoc "owl:hasValue" (printResource indUri))

    ObjectCardinality (Cardinality ty c opExp maybeDesc) ->
        tagToDoc "owl:Restriction"
         (cardinalityTag ty c $+$
          printOPERes opExp $+$
          maybe empty printOnClass maybeDesc)
    {-
      <owl:Restriction>
         <owl:onProperty rdf:resource="#hasChild"/>
         <owl11:onClass rdf:resource="#Female"/>
         <owl:minCardinality rdf:datatype="&xsd;nonNegativeInteger">2
         </owl:minCardinality>
      </owl:Restriction>
     -}
    DataValuesFrom ty dpExp dpExpList dRange ->
        tagToDoc "owl:Restriction"
           (listToDoc' (\d -> oneLineTagToDoc "owl:onProperty"
                              (printResource d)) (dpExp:dpExpList) $+$
            tagToDoc (quantifierType ty) (tagToDoc "rdf:Description"
                            (printRDF Map.empty  dRange)))
    {-
       <owl:Restriction>
          <owl:onProperty rdf:resource="#hasAge"/>
          <owl:allValuesFrom>
             ..  ..
          </owl:allValuesFrom>
       </owl:Restriction>
     -}
    DataHasValue dpExp cons ->
        tagToDoc "owl:Restriction"
           (oneLineTagToDoc "owl:onProperty" (printResource dpExp)$+$
            tagToDoc "owl:hasValue" (printRDF Map.empty  cons))
    DataCardinality (Cardinality ty c dpExp maybeRange) ->
        tagToDoc "owl:Restriction"
           (oneLineTagToDoc "owl:onProperty" (printResource dpExp) $+$
            cardinalityTag ty c $+$
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
         $+$ oneLineTagToDoc "owl:onDataRange"
                 (case drange of
                    DRDatatype u -> printResource u
                    _ -> error "unknown datatype.")
         $+$ (vcat $ map printFV l)

printOnClass :: Description -> Doc
printOnClass desc =
    case desc of
      OWLClass c -> oneLineTagToDoc "owl:onClass" (printResource c)
      _ -> text $ show desc   -- debug
    -- <owl11:onClass rdf:resource="#Female"/>


printFV :: (DatatypeFacet, RestrictionValue) -> Doc
printFV (facet, restValue) = printFacet facet
                                    (getValueFromConst restValue)

getValueFromConst :: Constant -> Doc
getValueFromConst (Constant lexi _) = text lexi

printFacet :: DatatypeFacet -> Doc -> Doc
printFacet facet doc =
    text "<" <> printRDF Map.empty facet <+> text "rdf:datatype=\"&xsd;int\">"
    <> doc <> text "</"<> printRDF Map.empty facet <> text ">"

instance PrettyRDF DatatypeFacet where
    printRDF _ df =
        case df of
          LENGTH -> text "owl:length"
          MINLENGTH -> text "owl:minLength"
          MAXLENGTH -> text "owl:maxLength"
          PATTERN -> text "owl:pattern"
          MININCLUSIVE -> text "owl:minInclusive"
          MINEXCLUSIVE -> text "owl:minExclusive"
          MAXINCLUSIVE -> text "owl:maxInclusive"
          MAXEXCLUSIVE -> text "owl:maxExclusive"
          TOTALDIGITS -> text "owl:totalDigits"
          FRACTIONDIGITS -> text "owl:fractionDigits"

instance PrettyRDF Constant where
    printRDF _ (Constant lexi ty) = case ty of
        Typed u -> text "<owl:Constant rdfs:Datatype=" <>
                  text (show$localPart u) <>
                  text (">" ++ lexi) <> text "</owl:Constant>"
   -- <Constant Datatype="&xsd;int">20</Constant>
        _ -> text "<owl:Constant>" <> text lexi <> text "</owl:Constant>"

instance PrettyRDF Entity where
    printRDF _ = printEntity

printEntity :: Entity -> Doc
printEntity (Entity ty eUri) = oneLineTagToDoc
    (case ty of
       Datatype -> "rdfs:Datatype"
       OWLClassEntity -> "owl:Class"
       ObjectProperty -> "owl:ObjectProperty"
       DataProperty -> "owl:DatatypeProperty"
       Individual -> "owl:Individual") (printURI eUri)

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
  EntityAnno _ -> empty    -- EntityAnnotation, here the "implied" comes
  PlainAxiom _ paxiom -> case paxiom of
   SubClassOf sub super ->
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

   EquivOrDisjointClasses Equivalent (clazz : equiList) ->
       printClass clazz
          (equivalentClassTag
             $ listToDoc' (\ d -> case d of
                 ObjectJunction IntersectionOf _ ->
                     (printRDF Map.empty  d)
                 ObjectOneOf _ -> (printRDF Map.empty  d)
                 _ -> printRDF Map.empty d) equiList)
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

   EquivOrDisjointClasses Disjoint (clazz : djList) ->
       tagToDocWithAttr' "owl:Class" (printURIFromDesc clazz)
         (tagToDoc "owl:disjointWith" (listToDoc' (printRDF Map.empty) djList))
    {-
     <owl:Class rdf:about="#Teenager">
         <owl:disjointWith rdf:resource="#Adult"/>
     </owl:Class>
    -}

   DisjointUnion curi discList ->
       tagToDocWithAttr' "owl:Class" (printURI curi)
         (tagToDocWithAttr "owl:disjointUnionOf"
          "rdf:parseType=\"Collection\""
          (listToDoc' (printRDF Map.empty) discList))
   {-
     <owl:Class rdf:about="#Person">
        <owl11:disjointUnionOf rdf:parseType="Collection">
            <rdf:Description rdf:about="#Female"/>
            <rdf:Description rdf:about="#Male"/>
        </owl11:disjointUnionOf>
     </owl:Class>
    -}

   -- ObjectPropertyAxiom
   SubObjectPropertyOf sopExp opExp ->
     case sopExp of
       OPExpression oexp ->
        tagToDocWithAttr' "owl:ObjectProperty" (printURIFromOPExp oexp)
           (tagToDoc "rdfs:subPropertyOf" (printRDF Map.empty opExp))
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

   EquivOrDisjointObjectProperties ty (opExp : opList) ->
       let tystr = case ty of
                     Equivalent -> "owl:equivalentProperty"
                     Disjoint -> "owl:disjointObjectProperties"
       in tagToDocWithAttr' "owl:ObjectProperty" (printURIFromOPExp opExp)
           (listToDoc' (\o -> oneLineTagToDoc tystr
                          (printURIFromOPExpRes o)) opList)
    {-
      <owl:ObjectProperty rdf:about="#hasSon">
        <rdfs:range rdf:resource="#Male"/>
        <owl:equivalentProperty rdf:resource="#hasSibling"/>
        <rdfs:subPropertyOf rdf:resource="#hasChild"/>
        <owl:equivalentProperty rdf:resource="#hasDaughter"/>
      </owl:ObjectProperty>
    -}

   ObjectPropertyDomainOrRange rd opExp desc ->
       let rdstr = "rdfs:" ++ case rd of
                     ObjDomain -> "domain"
                     ObjRange -> "range"
       in tagToDocWithAttr' "owl:ObjectProperty"
                             (printURIFromOPExp opExp)
          (case desc of
             OWLClass _ -> oneLineTagToDoc rdstr
                               (printURIFromDescRes desc)
             _ -> tagToDoc rdstr
                        (printRDF Map.empty desc))
    {-
      <owl:ObjectProperty rdf:about="#hasAncestor">
        <rdfs:domain rdf:resource="#Person"/>
        <rdfs:range rdf:resource="#Person"/>
      </owl:ObjectProperty>
    -}
   InverseObjectProperties opExp1 opExp2 ->
       tagToDocWithAttr' "owl:ObjectProperty"
                             (printURIFromOPExp opExp1)
          (oneLineTagToDoc "owl:inverseOf" (printURIFromOPExpRes opExp2))
    {-
      <owl:ObjectProperty rdf:about="#hasBrother">
        <owl:inverseOf rdf:resource="#hasSister"/>
      </owl:ObjectProperty>
    -}
   ObjectPropertyCharacter ch opExp ->
       let ver11 = case ch of
              Reflexive -> True
              Irreflexive -> True
              Asymmetric -> True
              _ -> False
           chstr = "<rdf:type rdf:resource=\"&owl" ++
                   (if ver11 then "11;" else ";") ++ show ch ++"Property\"/>"
        in tagToDocWithAttr' "owl:ObjectProperty" (printURIFromOPExp opExp)
               (text chstr)
    {-
      <owl:ObjectProperty rdf:about="#hasFather">
        <rdf:type rdf:resource="&owl;FunctionalProperty"/>
        <rdf:type rdf:resource="&owl11;AsymmetricProperty"/>
        <rdf:type rdf:resource="&owl;InverseFunctionalProperty"/>
        <rdf:type rdf:resource="&owl11;ReflexiveProperty"/>
        <rdf:type rdf:resource="&owl11;IrreflexiveProperty"/>
        <rdf:type rdf:resource="&owl;TransitiveProperty"/>
        <rdf:type rdf:resource="&owl;SymmetricProperty"/>
        <rdfs:subPropertyOf rdf:resource="#hasParent"/>
        <rdfs:range rdf:resource="#Male"/>
      </owl:ObjectProperty>
    -}

   -- DataPropertyAxiom
       -- no example
   SubDataPropertyOf dpExp1 dpExp2 ->
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
   EquivOrDisjointDataProperties ty (dpExp : dpList) ->
       let tystr = case ty of
                     Equivalent -> "owl:equivalentProperty"
                     Disjoint -> "owl:disjointDataProperties"
       in tagToDocWithAttr' "owl:DatatypeProperty" (printURI dpExp)
        (listToDoc' (oneLineTagToDoc tystr . printResource) dpList)
   DataPropertyDomainOrRange ddr dpExp ->
       let rdoc = case ddr of
             DataDomain desc ->
               tagToDoc "rdfs:domain" (printRDF Map.empty desc)
             DataRange drange -> case drange of
               DRDatatype did ->
                 oneLineTagToDoc "rdfs:range" (printResource did)
               _ -> tagToDoc "rdfs:range" (printRDF Map.empty drange)
       in tagToDocWithAttr' "owl:DatatypeProperty" (printURI dpExp) rdoc
    {-
      <owl:DatatypeProperty rdf:about="#testDataProperty1">
        <rdfs:domain rdf:resource="#Female"/>
      </owl:DatatypeProperty>
     -}
   FunctionalDataProperty dpExp ->
      tagToDocWithAttr' "owl:DatatypeProperty" (printURI dpExp)
        (text "<rdf:type rdf:resource=\"&owl;FunctionalProperty\"/>")

   -- Fact
   -- see http://www.w3.org/2007/OWL/draft/ED-owl11-xml-serialization-20080326/
   SameOrDifferentIndividual Same (ind : indList) ->
       case Map.lookup ind indClsMap of
         Just classId ->
             let clz = classNameForInd classId
             in tagToDocWithAttr' clz (printURI ind)
                    (listToDoc'
                     (\i -> oneLineTagToDoc "owl:sameAs"
                            (printResource i)) indList)
         Nothing ->
             tagToDoc "owl:SameIndividual"
                          ((printIndividual ind)
                           $+$ (listToDoc printIndividual indList))
    {-
      <Person rdf:about="#personX">
        <owl:sameAs rdf:resource="#uncle"/>
        <owl:sameAs rdf:resource="#father"/>
      </Person>
     -}
   SameOrDifferentIndividual Different indList ->
       tagToDoc "rdf:Description"
         (text "<rdf:type rdf:resource=\"&owl;AllDifferent\"/>" $+$
          tagToDocWithAttr "owl:distinctMembers"
          "rdf:parseType=\"Collection\""
          (listToDoc' (\d -> oneLineTagToDoc "rdf:Description" (printURI d))
           indList))
    {-
      <rdf:Description>
        <rdf:type rdf:resource="&owl;AllDifferent"/>
        <owl:distinctMembers rdf:parseType="Collection">
            <rdf:Description rdf:about="#personY"/>
            <rdf:Description rdf:about="#father"/>
        </owl:distinctMembers>
      </rdf:Description>
     -}
   ClassAssertion ind desc ->
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
           tagToDoc "owl2xml:ClassAssertion"
                ((case desc of
                    OWLClass ouri ->
                      text "<owl2xml:Class" <+> printResource ouri
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
   ObjectPropertyAssertion (Assertion opExp Positive source target) ->
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
             tagToDoc "owl2xml:ObjectPropertyAssertion"
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

   ObjectPropertyAssertion (Assertion opExp Negative source target) ->
       tagToDoc "owl2xml:NegativeObjectPropertyAssertion"
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

   DataPropertyAssertion (Assertion dpExp Positive source target) ->
       case Map.lookup source indClsMap of
         Just curi ->
             tagToDocWithAttr' (classNameForInd curi) (printURI source)
                  (printDPWithConst dpExp target)
         Nothing ->
             tagToDoc "owl2xml:DataPropertyAssertion"
                 (oneLineTagToDoc "owl2xml:DataProperty"
                        (printResource dpExp)
                  $+$ printIndividual source
                  $+$ printRDF Map.empty  target)
   {-
    <Person rdf:about="#father">
        <hasAge rdf:datatype="&xsd;int">38</hasAge>
    </Person>
   -}

   DataPropertyAssertion (Assertion dpExp Negative source target) ->
       tagToDoc "owl:2xmlNegativeDataPropertyAssertion"
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
   Declaration entity ->
     {-  case entity of ->
         Datatype u ->
         OWLClassEntity u
         ObjectProperty u
         DataProperty u
         Individual u
      -}
                (printRDF Map.empty  entity)
   u -> error ("unknow axiom" ++ show u)


instance PrettyRDF SubObjectPropertyExpression where
    printRDF _ sopExp =
        case sopExp of
          OPExpression opExp ->
              tagToDoc "rdfs:subPropertyOf" (printRDF Map.empty opExp)

          SubObjectPropertyChain opExpList ->
              tagToDoc "rdfs:subPropertyOf"
                (tagToDoc "owl:propertyChain"
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

printIndividual :: IndividualURI -> Doc
printIndividual iuri =
    oneLineTagToDoc "owl:Individual" (printResource iuri)

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
       InverseOp _ -> error
         "NegativeObjectPropertyAssertion can not accept inverse object"

printPredicateDataProp :: DataPropertyExpression -> Doc
printPredicateDataProp dpe =
    oneLineTagToDoc "rdf:predicate" (printResource dpe)

printObjectDataProp :: TargetValue -> Doc
printObjectDataProp (Constant lexi ety) =
    tagToDocWithAttr' "rdf:object" (printConstURIWithAttr ety) (text lexi)

printConstURIWithAttr :: TypedOrUntyped -> Doc
printConstURIWithAttr ety = case ety of
    Typed ty -> printURIWithAttr "rdf:datatype" ty
    _ -> empty

printDPWithConst :: DataPropertyExpression
                 -> Constant -> Doc
printDPWithConst dpe (Constant lexi ety) =
    tagToDocWithAttr' (localPart dpe) (printConstURIWithAttr ety) (text lexi)

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

nest :: Int -> Doc
nest longOfNest
    | longOfNest == 0 = empty
    | otherwise = space <> (nest (longOfNest -1))
