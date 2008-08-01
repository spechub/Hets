{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2004-2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(instances for URIreference and Namespace)

Pretty printing for OWL DL theories from abstract syntax to OWL file.
-}

module OWL.PrintOWL where

import Common.Doc
-- import Common.DocUtils
-- import qualified Common.Lib.Pretty as Pretty (nest, char)

import Text.XML.HXT.DOM.XmlTreeTypes (QName(..))
import OWL.Sign
import OWL.AS

import qualified Common.AS_Annotation as AS_Anno
-- import qualified Data.Set as Set
import qualified Data.Map as Map

class PrettyOWL a where
    printOWL  :: a -> Doc
--    printOWLs :: [a] -> Doc
--    printOWLs = brackets . ppWithCommas


instance PrettyOWL Sign where
    printOWL  = printOntologyHead

printOntologyHead :: Sign -> Doc
printOntologyHead sig =
    let ns = namespaceMap sig
        oID = ontologyID sig
    in  text "<?xml version=\"1.0\"?>" $++$
         printNamespace oID ns     $++$ nest 4 <>
         text "<owl:Ontology" <+> printOWL oID <> text ">" $+$ nest 4 <>
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


instance PrettyOWL URIreference where
    printOWL = printURI

printURI :: URIreference -> Doc
printURI (QN prefix localpart u)
  --  | localpart == "_" = text $ show "_"
    | null prefix = if null u then
                        text ("owl11xml:URI=" ++ show localpart)
                      else if null localpart then
                               text ("owl11xml:URI=" ++ show u)
                            else text ("owl11xml:URI=" ++
                                       show (u ++ ";" ++ localpart))
    | otherwise = text ("owl11xml:URI=" ++
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

instance PrettyOWL SignAxiom where
    printOWL = text . show     -- printSignAxiom ignored

instance PrettyOWL Description where
    printOWL = printDescription

printDescription :: Description -> Doc
printDescription desc = case desc of
   OWLClass ocUri -> text "<owl11xml:OWLClass" <+> printOWL ocUri
                     <+> text "/>"
   ObjectUnionOf descList ->
       tagToDoc "owl11xml:ObjectUnionOf"
                        (listToDoc printOWL descList)
   ObjectIntersectionOf descList ->
       tagToDoc "owl11xml:ObjectIntersectionOf"
            (listToDoc printOWL descList)
   {-
    <owl11xml:ObjectIntersectionOf>
      <owl11xml:OWLClass owl11xml:URI="#person"/>
      <owl11xml:ObjectSomeValuesFrom>
        <owl11xml:ObjectProperty owl11xml:URI="#drives"/>
        <owl11xml:OWLClass owl11xml:URI="#bus"/>
      </owl11xml:ObjectSomeValuesFrom>
    </owl11xml:ObjectIntersectionOf>
   -}

   ObjectComplementOf d ->
       tagToDoc "owl11xml:ObjectComplementOf"
                (printOWL d)
   ObjectOneOf indUriList ->
       tagToDoc "owl11xml:ObjectOneOf"
                (listToDoc printIndividual indUriList)
   ObjectAllValuesFrom opExp d ->
       tagToDoc "owl11xml:ObjectAllValuesFrom"
                (printOWL opExp $+$ printOWL d)
  {-
    <owl11xml:ObjectAllValuesFrom>
      <owl11xml:ObjectProperty owl11xml:URI="#reads"/>
      <owl11xml:OWLClass owl11xml:URI="#tabloid"/>
    </owl11xml:ObjectAllValuesFrom>
  -}
   ObjectSomeValuesFrom opExp d ->
       tagToDoc "owl11xml:ObjectSomeValuesFrom"
                (printOWL opExp $+$ printOWL d)
   ObjectExistsSelf opExp ->
       tagToDoc "owl11xml:ObjectExistsSelf"
                (printOWL opExp)
   ObjectHasValue opExp indUri ->
              tagToDoc "owl11xml:ObjectHasValue"
                (printOWL opExp $+$ printIndividual indUri)
   ObjectMinCardinality card opExp maybeDesc ->
       cardinalityToDoc "ObjectMinCardinality" card
         (printOWL opExp $+$ maybe empty printOWL maybeDesc)

  {-
      <owl11xml:ObjectMinCardinality owl11xml:cardinality="3">
        <owl11xml:ObjectProperty owl11xml:URI="#has_pet"/>
        <owl11xml:OWLClass owl11xml:URI="#dog"/>
      </owl11xml:ObjectMinCardinality>

  -}
   ObjectMaxCardinality card opExp maybeDesc ->
       cardinalityToDoc "ObjectMaxCardinality" card
         (printOWL opExp $+$ maybe empty printOWL maybeDesc)

   ObjectExactCardinality card opExp maybeDesc ->
       cardinalityToDoc "ObjectExactCardinality" card
         (printOWL opExp $+$ maybe empty printOWL maybeDesc)

   DataAllValuesFrom dpExp dpExpList dRange ->
       tagToDoc "owl11xml:DataAllValuesFrom"
          (printDataProperty dpExp $+$
             nest 4 <> listToDoc printDataProperty dpExpList $+$
           printOWL dRange)

   DataSomeValuesFrom  dpExp dpExpList dRange ->
       tagToDoc "owl11xml:DataSomeValuesFrom"
          (printDataProperty dpExp $+$
             nest 4 <> listToDoc printDataProperty dpExpList $+$
           printOWL dRange)

   DataHasValue dpExp cons ->
       tagToDoc "owl11xml:DataHasValue"
          (printDataProperty dpExp  $+$ nest 4 <>
           printOWL cons)

   DataMinCardinality card dpExp maybeRange ->
       cardinalityToDoc "DataMinCardinality" card
         (printDataProperty dpExp $+$
             nest 4 <> maybe empty printOWL maybeRange)

   DataMaxCardinality  card dpExp maybeRange ->
       cardinalityToDoc "DataMaxCardinality" card
         (printOWL dpExp $+$ nest 4 <> maybe empty printOWL maybeRange)

   DataExactCardinality  card dpExp maybeRange ->
       cardinalityToDoc "DataExactCardinality" card
         (printDataProperty dpExp $+$
              nest 4 <> maybe empty printOWL maybeRange)

instance PrettyOWL ObjectPropertyExpression where
    printOWL = printObjPropExp

printObjPropExp :: ObjectPropertyExpression -> Doc
printObjPropExp obExp =
    case obExp of
     OpURI ou -> text "<owl11xml:ObjectProperty" <+> printOWL ou
                 <> text "/>"
     InverseOp iopExp -> tagToDoc "owl11xml:InverseObjectProperty"
                            (printObjPropExp iopExp)

instance PrettyOWL DataRange where
    printOWL = printDataRange

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
  tagToDoc "rdfs:range"
  (tagToDoc "owl:DataRange"
   (case dr of
    DRDatatype du ->
        oneLineTagToDoc "Datatype"
                                 (printOWL du)
         --  <Datatype URI="&rdfs;Literal"/>
    DataComplementOf drange ->
        tagToDoc "owl11xml:DataComplementOf"
                 (printOWL drange)
    DataOneOf constList ->
        text "<owl:oneOf rdf:parseType=\"Resource\">" $+$nest 4 <>
          listToDoc printOWL constList $+$
        text "</owl:oneOf>"
    DatatypeRestriction drange l ->
        tagToDoc "DatatypeRestriction"
          (printOWL drange $+$ (vcat $ map printFV l))
   ))
    {-
     <DatatypeRestriction>
       <Datatype URI="&xsd;nonNegativeInteger"/>
       <DatatypeFacetRestriction facet="&owl11;minInclusive">
            <Constant Datatype="&xsd;int">10</Constant>
       </DatatypeFacetRestriction>
       <DatatypeFacetRestriction facet="&owl11;maxExclusive">
            <Constant Datatype="&xsd;int">20</Constant>
       </DatatypeFacetRestriction>
     </DatatypeRestriction>
    -}

printFV :: (DatatypeFacet, RestrictionValue) -> Doc
printFV (facet, restValue) = printFacet facet
                                    (printOWL restValue)

printFacet :: DatatypeFacet -> Doc -> Doc
printFacet facet doc =
    (text "<DatatypeFacetRestriction facet=\"&owl11;" <>
         printOWL facet <> text "\">") $+$ nest 4 <>
      doc $+$
    text "</DatatypeFacetRestriction>"

instance PrettyOWL DatatypeFacet where
    printOWL = text . show

instance PrettyOWL Constant where
    printOWL cons =
        case cons of
          TypedConstant (lexi, u) ->
              text "<Constant Datatype=" <> (text $ show$localPart u) <>
                   text (">" ++ lexi) <> text "</Constant>"
   -- <Constant Datatype="&xsd;int">20</Constant>
          UntypedConstant (lexi, _) ->
              text "<Constant>" <>
                   (text $ lexi) <> (text "</Constant>")


instance PrettyOWL Entity where
    printOWL = printEntity

printEntity :: Entity -> Doc
printEntity entity =
    case entity of
       Datatype dUri ->
           oneLineTagToDoc "DataProperty" (printOWL dUri)
           -- <DataProperty URI="&family;hasAge"/>
       OWLClassEntity cUri ->
           oneLineTagToDoc "OWLClass" (printOWL cUri)
           -- <owl11xml:OWLClass owl11xml:URI="#animal"/>
       ObjectProperty opUri ->
           oneLineTagToDoc "ObjectProperty" (printOWL opUri)
           -- <owl11xml:ObjectProperty owl11xml:URI="#eats"/>
       DataProperty dpUri ->
           printDataProperty dpUri
       Individual iUri ->
           printIndividual iUri
           -- oneLineTagToDoc "Individual URI=" (printOWL iUri)

instance PrettyOWL Sentence where
    printOWL = printSentence

printSentence :: Sentence -> Doc
printSentence sent = case sent of
    OWLAxiom axiom -> nest 4 <> printOWL axiom
    OWLFact fact   -> nest 4 <> printOWL fact

instance PrettyOWL Axiom where
    printOWL = printAxiom

printAxiom :: Axiom -> Doc
printAxiom axiom = case axiom of
   SubClassOf _ sub super ->
       classTag sub
                    (tagToDoc "rdfs:subClassOf" (printOWL super))
   EquivalentClasses _ (clazz:equiList) ->
       classTag clazz
                (tagToDoc "owl:equivalentClass"
                              (listToDoc printOWL equiList))
   DisjointClasses _ (clazz:djList) ->
       classTag clazz
                (tagToDoc "owl:disjointClass" (listToDoc printOWL djList))
   DisjointUnion _ curi discList ->
       classTag' curi
                (tagToDocWithAttr
                 "owl11:disjointUnionOf" "rdf:parseType=\"Collection\""
                 (listToDoc printOWL discList))
   -- ObjectPropertyAxiom
   SubObjectPropertyOf _ sopExp opExp ->
       tagToDoc "owl11xml:SubObjectPropertyOf"
           (printOWL sopExp $+$ printOWL opExp)
   EquivalentObjectProperties _ (opExp:opList) ->
       tagToDoc "owl11xml:EquivalentObjectProperties"
           (printOWL opExp $+$ (listToDoc printOWL opList))
   DisjointObjectProperties _ (opExp:opList) ->
       tagToDoc "owl11xml:DisjointObjectProperties"
           (printOWL opExp $+$ (listToDoc printOWL opList))
   ObjectPropertyDomain _ opExp desc ->
       tagToDoc "owl11xml:ObjectPropertyDomain"
           (printOWL opExp $+$ printOWL desc)
   ObjectPropertyRange  _ opExp desc ->
       tagToDoc "owl11xml:ObjectPropertyRange"
           (printOWL opExp $+$ printOWL desc)
   InverseObjectProperties  _ opExp1 opExp2 ->
       tagToDoc "owl11xml:InverseObjectProperties"
           (printOWL opExp1 $+$ printOWL opExp2)
   FunctionalObjectProperty _ opExp ->
       tagToDoc "owl11xml:FunctionalObjektProperty"
           (printOWL opExp)           -- no example
   InverseFunctionalObjectProperty _ opExp ->
       tagToDoc "owl11xml:InverseFunctionalObjektProperty"
           (printOWL opExp)           -- no example
   ReflexiveObjectProperty  _ opExp ->
       tagToDoc "owl11xml:ReflexiveObjectProperty"
           (printOWL opExp)           -- no example
   IrreflexiveObjectProperty  _ opExp ->
       tagToDoc "owl11xml:IrreflexiveObjectProperty"
           (printOWL opExp)           -- no example
   SymmetricObjectProperty  _ opExp ->
       tagToDoc "owl11xml:SymmetricObjectProperty"
           (printOWL opExp)
   AntisymmetricObjectProperty  _ opExp ->
       tagToDoc "owl11xml:AntisymmetricObjectProperty"
           (printOWL opExp)
   TransitiveObjectProperty _ opExp ->
       tagToDoc "owl11xml:TransitiveObjectProperty"
           (printOWL opExp)
   -- DataPropertyAxiom
       -- no example
   SubDataPropertyOf _ dpExp1 dpExp2 ->
       tagToDoc "owl11xml:SubDataPropertyOf"
           (printDataProperty dpExp1 $+$ printDataProperty dpExp2)
   EquivalentDataProperties  _ (dpExp:dpList) ->
       tagToDoc "owl11xml:EquivalentDataProperties"
           (printDataProperty dpExp
            $+$ (listToDoc printDataProperty dpList))
   DisjointDataProperties  _ (dpExp:dpList) ->
       tagToDoc "owl11xml:DisjointDataProperties"
           (printDataProperty dpExp
            $+$ (listToDoc printDataProperty dpList))
   DataPropertyDomain  _ dpExp desc ->
       tagToDoc "owl11xml:DataPropertyDomain"
           (printDataProperty dpExp $+$ printOWL desc)
   DataPropertyRange  _ dpExp desc ->
       tagToDoc "owl11xml:DataPropertyRange"
           (printDataProperty dpExp $+$ printOWL desc)
   FunctionalDataProperty _ dpExp ->
       tagToDoc "owl11xml:FunctionalDataProperty"
           (printDataProperty dpExp)

   -- Fact
   -- see http://www.w3.org/2007/OWL/draft/ED-owl11-xml-serialization-20080326/#The_XML_Schema
   SameIndividual _ (ind:indList) ->
       tagToDoc "owl11xml:SameIndividual"
           ((printIndividual ind)
            $+$ (listToDoc printIndividual indList))
   DifferentIndividuals _ (ind:indList) ->
       tagToDoc "owl11xml:DifferentIndividuals"
           (printIndividual ind $+$ listToDoc printIndividual indList)
       -- <ox:Individual ox:URI="#person"/>

   ClassAssertion _ ind desc ->
       tagToDoc "owl11xml:ClassAssertion"
           (printOWL desc $+$ printIndividual ind)
   ObjectPropertyAssertion _ opExp source target ->
       tagToDoc "owl11xml:ObjectPropertyAssertion"
           (printOWL opExp $+$ printIndividual source
                         $+$ printIndividual target)
   NegativeObjectPropertyAssertion  _ opExp source target ->
       tagToDoc "owl11xml:NegativeObjectPropertyAssertion"
           (printOWL opExp $+$ printIndividual source
                         $+$ printIndividual target)
   DataPropertyAssertion  _ dpExp source target ->
       tagToDoc "owl11xml:DataPropertyAssertion"
           (oneLineTagToDoc "owl11xml:DataProperty" (printOWL dpExp)
            $+$ printIndividual source
            $+$ printOWL target)
   NegativeDataPropertyAssertion  _ dpExp source target ->
       tagToDoc "owl11xml:NegativeDataPropertyAssertion"
           (printOWL dpExp $+$ printIndividual source
                         $+$ printOWL target)
   Declaration _ entity ->
       tagToDoc "Declaration"
                (printOWL entity)
   EntityAnno _ -> empty       -- EntityAnnotation, here the "implied" comes
   u -> error ("unknow axiom" ++ show u)


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
        text "<owl11xml:OWLClass" <+> printOWL cu
                          <+> text ">"

    classEnd :: Doc
    classEnd = text "</owl11xml:OWLClass>"

classTag' :: OwlClassURI -> Doc -> Doc
classTag' curi d =
    classTag (OWLClass curi) d

printIndividual :: IndividualURI -> Doc
printIndividual iuri =
    oneLineTagToDoc "owl11xml:Individual" (printOWL iuri)

printDataProperty :: DataPropertyExpression -> Doc
printDataProperty dpe =
    oneLineTagToDoc "DataProperty" (printOWL dpe)

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


cardinalityToDoc :: String -> Cardinality -> Doc -> Doc
cardinalityToDoc tag card d =
    text ("<owl11xml:" ++ tag ++ " owl11xml:cardinality=\"" ++
                       show card ++ "\">") $+$
       nest 4 <> d  $+$
    text ("</owl11xml:" ++ tag ++ ">")

oneLineTagToDoc :: String -> Doc -> Doc
oneLineTagToDoc s content =
    text ("<" ++ s) <+> content <> text "/>"

instance PrettyOWL SubObjectPropertyExpression where
    printOWL sopExp =
        case sopExp of
          OPExpression opExp ->
              printOWL opExp
          SubObjectPropertyChain opExpList ->
              tagToDoc "owl11xml:SubObjectPropertyChain"
                 (listToDoc printOWL opExpList)

 {-
    <ox:SubObjectPropertyChain>
      <ox:ObjectProperty ox:URI="#owns"/>
      <ox:ObjectProperty ox:URI="#has_part"/>
    </ox:SubObjectPropertyChain>
 -}

-- not necessary
instance PrettyOWL OntologyFile where
    printOWL = text . show

instance PrettyOWL Ontology where
    printOWL = text . show  -- printOntology

instance PrettyOWL [AS_Anno.Named Sentence] where
    printOWL l = foldl ($+$) empty $ map printOWL l

instance PrettyOWL (AS_Anno.Named Sentence) where
    printOWL = printOWL . AS_Anno.sentence

listToDoc :: (PrettyOWL a) =>
             (a -> Doc) -> [a] -> Doc
listToDoc _ [] = empty
listToDoc p (lastOne:[]) =
      text ("<rdf:rest " ++
       "rdf:resource=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#nil\"/>")
    $+$ (tagToDoc "rdf:first" (p lastOne))
{-
        <owl:oneOf rdf:parseType="Resource">
          <rdf:rest
rdf:resource="http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"/>
          <rdf:first
rdf:datatype="http://www.w3.org/2001/XMLSchema#string"
          >78</rdf:first>
        </owl:oneOf>
-}
listToDoc p (h:r) =
    text "<rdf:rest rdf:parseType=\"Resource\">" $+$
       nest 4 <> listToDoc p r $+$
    text "</rdf:rest>" $+$
    (tagToDoc "rdf:first" (p h))
    {-
        <owl:oneOf rdf:parseType="Resource">
          <rdf:rest rdf:parseType="Resource">
            <rdf:rest rdf:parseType="Resource">
              <rdf:first
rdf:datatype="http://www.w3.org/2001/XMLSchema#int"
              >4</rdf:first>
              <rdf:rest
rdf:resource="http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"/>
            </rdf:rest>
            <rdf:first
rdf:datatype="http://www.w3.org/2001/XMLSchema#int"
            >3</rdf:first>
          </rdf:rest>
          <rdf:first rdf:datatype="http://www.w3.org/2001/XMLSchema#int"
          >2</rdf:first>
        </owl:oneOf>
    -}


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
