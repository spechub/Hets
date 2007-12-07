{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(instances for URIreference and Namespace)

Pretty printing for OWL DL theories.
-}

module OWL.Print where

import Common.Doc
import Common.DocUtils

import Text.XML.HXT.DOM.XmlTreeTypes (QName(QN))
import OWL.Sign
import OWL.AS

import qualified Data.Set as Set
import qualified Data.Map as Map

instance Pretty Sign where
    pretty = printSign

printSign :: Sign -> Doc
printSign (Sign _ p2 p3 p4 p5 p6 _ p8 p9 p10) =
    text "namespaces " $+$ printNamespace p10 $+$
    text "concepts" <+> setToDocF p2 $+$
    text "primaryConcepts " <+> setToDocF p3 $+$
    text "datatypes " <+> setToDocF p4 $+$
    text "indvidual_valued_roles " <+> setToDocF p5 $+$
    text "data_valued_roles " <+> setToDocF p6 $+$
    text "individuals " <+> setToDocF p8 $+$
    text "sign_axioms" $+$ vcat (setToDocs p9)

instance Pretty URIreference where
    pretty = printURIreference

printURIreference :: URIreference -> Doc
printURIreference (QN prefix localpart u)
    | localpart == "_" = text $ show "_"
    | null prefix = if null u then
                           text localpart
                           else text $ show (u ++ ":" ++ localpart)
    | otherwise =   text $ show ( prefix ++ ":" ++ localpart)

printNamespace :: Namespace -> Doc
printNamespace nsMap =
    vcat $ map pp (Map.toList nsMap)
       where pp :: (String, String) -> Doc
             pp (s1,s2) = text s1 <> defn <> text s2


instance Pretty SignAxiom where
    pretty = text . show -- printSignAxiom

{-
printSignAxiom :: SignAxiom -> Doc
printSignAxiom signAxiom = case signAxiom of
    Subconcept cid1 cid2 ->
      parens (text "forall ((x owl:Thing))" <+>
              parens (text "implies" <+>
                      parens (printDescription cid1 <+> text "x") <+>
                      parens (printDescription cid2 <+> text "x")))
    RoleDomain rid rdomains ->
      listToDocH
        (\x y -> parens (text "forall ((x owl:Thing) (y owl:Thing))" $+$
                         parens (text "implies" <+>
                                 parens (printURIreference x <+>
                                         text "x y") <+>
                                 (parens $ printRDomain y)))
        ) rid rdomains
    RoleRange rid rranges -> case head rranges of
      RDRange _ ->
        text "(forall ((x owl:Thing) (y rdfs:Literal))" $+$
        text "(implies (" <> printURIreference rid <+> text "x y)" $+$
        (if (length rranges > 1) then
           text "(or "
         else lparen) <>
        listToDocH form5 rid rranges $+$ text ")))"
      _         ->
        listToDocV
          (\x y -> text "(forall ((x owl:Thing) (y owl:Thing))" $+$
                   text "(implies (" <> printURIreference x <+>
                   text "x y) (" <> printRRange y <> text " y)" $+$
                   text "))")
          rid rranges
    FuncRole (rtype, rid) ->
      case rtype of
        IRole ->
          text "(forall ((x owl:Thing) (y owl:Thing) (z owl:Thing))" $+$
          text "(implies" $+$
          text "(and (" <> printURIreference rid <+>
          text "x y) (" <+> printURIreference rid <+> text "x z))" $+$
          text "(= y z)" $+$ text "))"
        DRole ->
          text "(forall ((x owl:Thing) (y rdfs:Literal) (z rdfs:Literal))" $+$
          text "(implies" $+$
          text "(and (" <> printURIreference rid <+>
          text "x y) (" <+> printURIreference rid <+> text "x z))" $+$
          text "(= y z)" $+$ text "))"
    Conceptmembership iID desc ->
      parens (printDescription 0 iID desc <+> printURIreference iID)
    u -> text . show u

printDescription :: Description -> Doc
printDescription desc = case desc of
   OWLClass ocUri -> printURIreference ocUri
   ObjectUnionOf descList -> setToDocs $ Set.fromList
                                 $ map printDescription descList
   ObjectIntersectionOf descList -> setToDocs $ Set.fromList
                                 $ map printDescription descList
   ObjectComplementOf Description
   ObjectOneOf [IndividualURI]  --  min. 1 Individual
   ObjectAllValuesFrom ObjectPropertyExpression Description
   ObjectSomeValuesFrom ObjectPropertyExpression Description
   ObjectExistsSelf ObjectPropertyExpression
   ObjectHasValue ObjectPropertyExpression IndividualURI
   ObjectMinCardinality Cardinality ObjectPropertyExpression (Maybe Description)
   ObjectMaxCardinality Cardinality ObjectPropertyExpression (Maybe Description)
   ObjectExactCardinality Cardinality ObjectPropertyExpression (Maybe Description)
   DataAllValuesFrom DataPropertyExpression [DataPropertyExpression] DataRange
   DataSomeValuesFrom DataPropertyExpression [DataPropertyExpression] DataRange
   DataHasValue DataPropertyExpression Constant
   DataMinCardinality Cardinality DataPropertyExpression (Maybe DataRange)
   DataMaxCardinality Cardinality DataPropertyExpression (Maybe DataRange)
   DataExactCardinality Cardinality DataPropertyExpression (Maybe DataRange)
-}

instance Pretty Sentence where
    pretty = text . show -- printSentence
{-
printSentence :: Sentence -> Doc
printSentence sent = case sent of
    OWLAxiom axiom -> printAxiom axiom
    OWLFact fact   -> printFact fact

printSentence :: Axiom -> Doc
printSentence axiom = case axiom of
   SubClassOf _ sub super ->
   EquivalentClasses [Annotation] [Description] -- min. 2 desc.
   DisjointClasses [Annotation] [Description] -- min. 2 desc.
   DisjointUnion [Annotation] OwlClassURI [Description] -- min. 2 desc.
           -- ObjectPropertyAxiom
   SubObjectPropertyOf [Annotation] SubObjectPropertyExpression ObjectPropertyExpression
   EquivalentObjectProperties [Annotation] [ObjectPropertyExpression]
                                  -- min. 2  ObjectPropertyExpression
   DisjointObjectProperties [Annotation] [ObjectPropertyExpression]
                                  -- min. 2  ObjectPropertyExpression
   ObjectPropertyDomain [Annotation] ObjectPropertyExpression Description
   ObjectPropertyRange [Annotation] ObjectPropertyExpression Description
   InverseObjectProperties [Annotation] ObjectPropertyExpression ObjectPropertyExpression
   FunctionalObjectProperty [Annotation] ObjectPropertyExpression
   InverseFunctionalObjectProperty [Annotation] ObjectPropertyExpression
   ReflexiveObjectProperty [Annotation] ObjectPropertyExpression
   IrreflexiveObjectProperty [Annotation] ObjectPropertyExpression
   SymmetricObjectProperty [Annotation] ObjectPropertyExpression
   AntisymmetricObjectProperty [Annotation] ObjectPropertyExpression
   TransitiveObjectProperty [Annotation] ObjectPropertyExpression
         -- DataPropertyAxiom
   SubDataPropertyOf [Annotation] DataPropertyExpression DataPropertyExpression
   EquivalentDataProperties [Annotation] [DataPropertyExpression]
                              -- min. 2 DataPropertyExpressions
   DisjointDataProperties [Annotation] [DataPropertyExpression]
                                  -- min. 2 DataPropertyExpressions
   DataPropertyDomain [Annotation] DataPropertyExpression Description
   DataPropertyRange [Annotation] DataPropertyExpression
instance Pretty SignAxiom where
    pretty = text . show -- printSignAxiom
 DataRange
   FunctionalDataProperty [Annotation] DataPropertyExpression
           -- Fact
   SameIndividual [Annotation] [IndividualURI]  -- min. 2 ind.
   DifferentIndividuals [Annotation] [IndividualURI]  -- min. 2 ind.
   ClassAssertion [Annotation] IndividualURI Description
   ObjectPropertyAssertion [Annotation] ObjectPropertyExpression SourceIndividualURI TargetIndividualURI
   NegativeObjectPropertyAssertion [Annotation] ObjectPropertyExpression SourceIndividualURI TargetIndividualURI
   DataPropertyAssertion [Annotation] DataPropertyExpression SourceIndividualURI TargetValue
   NegativeDataPropertyAssertion [Annotation] DataPropertyExpression SourceIndividualURI TargetValue
   Declaration [Annotation] Entity
   EntityAnno EntityAnnotation
-}

-- not necessary
instance Pretty OntologyFile where
    pretty = text . show
instance Pretty Ontology where
    pretty = text . show  -- printOntology

instance Pretty Axiom where
    pretty = text . show   -- printAxiom

setToDocs :: Pretty a => Set.Set a -> [Doc]
setToDocs = punctuate comma . map pretty . Set.toList

setToDocF :: Pretty a => Set.Set a -> Doc
setToDocF = fsep . setToDocs

setToDocV :: (Pretty a) => Set.Set a -> Doc
setToDocV = vcat . setToDocs

-- output a list in vertikal direction
listToDocV :: (Pretty a, Pretty b)
                  => (a -> b -> Doc) -> a -> [b] -> Doc
listToDocV printForm iD = vcat . map (printForm iD)

-- output a list in horizonal direction
listToDocH :: (Pretty a, Pretty b)
                  =>  (a -> b -> Doc) -> a -> [b] -> Doc
listToDocH printForm iD = hsep . map (printForm iD)


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
