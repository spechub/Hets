{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(instances for URIreference and Namespace)

Pretty printing for OWL DL theories.
-}

module OWL.Print () where

import Common.Doc
import Common.DocUtils

import OWL.Sign
import OWL.AS

import qualified Data.Set as Set
import qualified Data.Map as Map

instance Pretty Sign where
    pretty = printSign

printSign :: Sign -> Doc
printSign (Sign _ p2 p3 p4 p5 p6 _ p8 _ p10) =
    text "namespaces " $+$ printNamespace p10 $+$
    text "concepts" <+> setToDocF p2 $+$
    text "primaryConcepts " <+> setToDocF p3 $+$
    text "datatypes " <+> setToDocF p4 $+$
    text "indvidual_valued_roles " <+> setToDocF p5 $+$
    text "data_valued_roles " <+> setToDocF p6 $+$
    text "individuals " <+> setToDocF p8

instance Pretty URIreference where
    pretty = printURIreference

printURIreference :: URIreference -> Doc
printURIreference (QN prefix localpart u)
    | localpart == "_" = text $ show "_"
    | null prefix = if null u then
                        text localpart
                      else text $ show (u ++ ":" ++ localpart)
    | otherwise = text $ show ( prefix ++ ":" ++ localpart)

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
-}

instance Pretty Description where
    pretty = printDescription

printDescription :: Description -> Doc
printDescription desc = case desc of
   OWLClass ocUri -> printURIreference ocUri
   ObjectUnionOf descList ->
       text "or:" <+> sepByCommas (setToDocs $ Set.fromList descList)
   ObjectIntersectionOf descList ->  printDescriptionWithRestriction descList
   ObjectComplementOf d -> text "not" <+> pretty d
   ObjectOneOf indUriList -> specBraces $ setToDocF $ Set.fromList indUriList
   ObjectAllValuesFrom opExp d -> printObjPropExp opExp <+> text "only"
                                      <+> pretty d
   ObjectSomeValuesFrom opExp d -> printObjPropExp opExp <+> text "some"
                                       <+> pretty d
   ObjectExistsSelf opExp -> printObjPropExp opExp <+> text "some"
                                                   <+> text "self"
   ObjectHasValue opExp indUri -> pretty opExp  <+> text "value"
                                        <+> pretty indUri
   ObjectMinCardinality card opExp maybeDesc ->
        printObjPropExp opExp  <+> text "min" <+> (text $ show card) <+>
                            (maybe empty pretty maybeDesc)
   ObjectMaxCardinality card opExp maybeDesc ->
        printObjPropExp opExp  <+> text "max" <+> (text $ show card) <+>
                            (maybe empty pretty maybeDesc)
   ObjectExactCardinality card opExp maybeDesc ->
        printObjPropExp opExp  <+> text "exactly" <+> (text $ show card) <+>
                            (maybe empty pretty maybeDesc)
   DataAllValuesFrom dpExp dpExpList dRange ->
       printURIreference dpExp <+> text "only"
           <+> (if null dpExpList then empty
                 else specBraces (sepByCommas $ setToDocs
                   (Set.fromList dpExpList))) <+> pretty dRange
   DataSomeValuesFrom  dpExp dpExpList dRange ->
       printURIreference dpExp <+> text "some"
           <+> (if null dpExpList then empty
                   else specBraces (sepByCommas $ setToDocs
                         (Set.fromList dpExpList))) <+> pretty dRange
   DataHasValue dpExp cons -> pretty dpExp <+> text "value" <+> pretty cons
   DataMinCardinality  card dpExp maybeRange ->
        pretty dpExp  <+> text "min" <+> (text $ show card) <+>
                            (maybe empty pretty maybeRange)
   DataMaxCardinality  card dpExp maybeRange ->
        pretty dpExp  <+> text "max" <+> (text $ show card) <+>
                            (maybe empty pretty maybeRange)
   DataExactCardinality  card dpExp maybeRange ->
        pretty dpExp  <+> text "exactly" <+> (text $ show card) <+>
                            (maybe empty pretty maybeRange)

printDescriptionWithRestriction :: [Description] -> Doc
printDescriptionWithRestriction descList =
    writeDesc descList True False empty
  where
    writeDesc [] _ _ doc = doc
    writeDesc (h:r) isFirst lastWasNamed doc =
     let thisIsNamed = (case h of
                         OWLClass _ -> True
                         _ -> False)
     in  if isFirst then
             writeDesc r False thisIsNamed (printDescription h)

          else if not lastWasNamed then
                   writeDesc r False thisIsNamed
                          (doc $+$ text "and" <+> (printDescription h))
                else
                   writeDesc r False thisIsNamed
                    ((case h of
                       OWLClass _ -> doc $+$ text "and"
                       ObjectUnionOf _ -> doc $+$ text "and"
                       ObjectIntersectionOf _ -> doc $+$ text "and"
                       ObjectComplementOf _ -> doc $+$ text "and"
                       ObjectOneOf _ -> doc $+$ text "and"
                       _ -> doc $+$ text "that") <+> (printDescription h))

instance Pretty ObjectPropertyExpression where
    pretty = printObjPropExp

printObjPropExp :: ObjectPropertyExpression -> Doc
printObjPropExp obExp =
    case obExp of
     OpURI ou -> pretty ou
     InverseOp iopExp -> text "inverse" <> parens (printObjPropExp iopExp)

instance Pretty DataRange where
    pretty = printDataRange

printDataRange :: DataRange -> Doc
printDataRange dr = case dr of
    DRDatatype du -> pretty du
    DataComplementOf drange -> text "not" <+> pretty drange
    DataOneOf constList -> specBraces $ sepByCommas $ map pretty constList
    DatatypeRestriction drange l ->
        pretty drange <+> brackets (sepByCommas $ printFV l)

printFV :: [(DatatypeFacet, RestrictionValue)] -> [Doc]
printFV [] = []
printFV ((facet, restValue):r) = (pretty facet <> text ":"
                                  <+> pretty restValue):(printFV r)

instance Pretty DatatypeFacet where
    pretty = text . show

instance Pretty Constant where
    pretty cons = case cons of
                    TypedConstant (lexi, u) ->
                        text lexi <> text "^^" <> pretty u
                    UntypedConstant (lexi, tag) ->
                        text lexi <> text "@@" <> text tag

instance Pretty Sentence where
    pretty = printSentence

printSentence :: Sentence -> Doc
printSentence sent = case sent of
    OWLAxiom axiom -> pretty axiom
    OWLFact fact   -> pretty fact

instance Pretty Axiom where
    pretty = printAxiom

printAxiom :: Axiom -> Doc
printAxiom axiom = case axiom of
   SubClassOf _ sub super ->
       classStart <+> pretty sub $+$ (text "SubClassOf:") $+$
                   (pretty super)
   EquivalentClasses _ (clazz:equiList) ->
       classStart <+> pretty clazz $+$  (text "EquivalentTo:") $+$
                      (setToDocV $ Set.fromList equiList)

   DisjointClasses _ (clazz:equiList) ->
       classStart <+> pretty clazz $+$  (text "DisjointWith:") $+$
                   (setToDocV $ Set.fromList equiList)
   DisjointUnion _ curi discList ->
       classStart <+> pretty curi $+$  (text "DisjointUnionOf:") $+$
                   (setToDocV $ Set.fromList discList)
   -- ObjectPropertyAxiom
   SubObjectPropertyOf _ sopExp opExp ->
       opStart <+> pretty sopExp $+$  (text "SubObjectPropertyOf:") $+$
                (pretty opExp)
   EquivalentObjectProperties _ (opExp:opList) ->
       opStart <+> pretty opExp $+$  (text "EquivalentTo:") $+$
                   (setToDocV $ Set.fromList opList)
   DisjointObjectProperties _ (opExp:opList) ->
       opStart <+> pretty opExp $+$  (text "DisjointWith:") $+$
                   (setToDocV $ Set.fromList opList)
   ObjectPropertyDomain _ opExp desc ->
       opStart <+> pretty opExp $+$  (text "Domain:") $+$
                   (pretty desc)
   ObjectPropertyRange  _ opExp desc ->
       opStart <+> pretty opExp $+$  (text "Range:") $+$
                   (pretty desc)
   InverseObjectProperties  _ opExp1 opExp2 ->
       opStart <+> pretty opExp1 $+$  (text "Inverse:") $+$
                   (pretty opExp2)
   FunctionalObjectProperty _ opExp ->
       opStart <+> pretty opExp $+$  (printCharact "Functinal")
   InverseFunctionalObjectProperty _ opExp ->
       opStart <+> pretty opExp $+$  (printCharact "Inverse_Functinal")
   ReflexiveObjectProperty  _ opExp ->
       opStart <+> pretty opExp $+$  (printCharact "Reflexive")
   IrreflexiveObjectProperty  _ opExp ->
       opStart <+> pretty opExp $+$  (printCharact "Irreflexive")
   SymmetricObjectProperty  _ opExp ->
       opStart <+> pretty opExp $+$  (printCharact "Symmetric")
   AntisymmetricObjectProperty  _ opExp ->
       opStart <+> pretty opExp $+$  (printCharact "AntiSymmetric")
   TransitiveObjectProperty _ opExp ->
       opStart <+> pretty opExp $+$  (printCharact "Transitive")
   -- DataPropertyAxiom
   SubDataPropertyOf _ dpExp1 dpExp2 ->
       dpStart <+> pretty dpExp1 $+$  (text "SubDataPropertyOf") $+$
                (pretty dpExp2)
   EquivalentDataProperties  _ (dpExp:dpList) ->
       opStart <+> pretty dpExp $+$  (text "EquivalentTo:") $+$
                (setToDocV $ Set.fromList dpList)
   DisjointDataProperties  _ (dpExp:dpList) ->
       opStart <+> pretty dpExp $+$  (text "DisjointWith:") $+$
                   (setToDocV $ Set.fromList dpList)
   DataPropertyDomain  _ dpExp desc ->
       opStart <+> pretty dpExp $+$  (text "Domain:") $+$
                   (pretty desc)
   DataPropertyRange  _ dpExp desc ->
       opStart <+> pretty dpExp $+$  (text "Range:") $+$
                   (pretty desc)
   FunctionalDataProperty _ dpExp ->
       opStart <+> pretty dpExp $+$  (printCharact "Functinal")
   -- Fact
   SameIndividual _ (ind:indList) ->
       indStart <+> (pretty ind) $+$  (text "SameAs:") $+$
                 (setToDocV $ Set.fromList indList)
   DifferentIndividuals _ (ind:indList) ->
       indStart <+> (pretty ind) $+$  (text "DifferentFrom:") $+$
                 (setToDocV $ Set.fromList indList)
   ClassAssertion _ ind desc ->
       indStart <+> (pretty ind) $+$  (text "Types:") $+$
                 (pretty desc)
   ObjectPropertyAssertion _ opExp source target ->
       indStart <+> (pretty source) $+$  (pretty opExp) $+$
                 (pretty target)
   NegativeObjectPropertyAssertion  _ opExp source target ->
       indStart <+> (pretty source) $+$  (text "not" <+>
                                  parens (pretty opExp <+> pretty target))
   DataPropertyAssertion  _ dpExp source target ->
       indStart <+> (pretty source) $+$  (pretty dpExp) $+$
                 (pretty target)
   NegativeDataPropertyAssertion  _ dpExp source target ->
       indStart <+> (pretty source) $+$  (text "not" <+>
                                  parens (pretty dpExp <+> pretty target))
   Declaration _ _ -> empty    -- [Annotation] Entity
   EntityAnno _ -> empty -- EntityAnnotation
   u -> error ("unknow axiom" ++ show u)

classStart :: Doc
classStart = text "Class:"

opStart :: Doc
opStart = text "ObjectProterty:"

dpStart :: Doc
dpStart = text "DataProperty:"

indStart :: Doc
indStart = text "Individual:"

printCharact :: String -> Doc
printCharact charact =
    text "Characteristics:" $+$  (text charact)

instance Pretty SubObjectPropertyExpression where
    pretty sopExp =
        case sopExp of
          OPExpression opExp -> pretty opExp
          SubObjectPropertyChain opExpList ->
              foldl (\x y -> x <+> text "o" <+> y)
                  empty (setToDocs (Set.fromList $
                                 take (length opExpList -1) opExpList)) <+>
                  text "o" <+> pretty (head $ reverse opExpList)

-- not necessary
instance Pretty OntologyFile where
    pretty = text . show

instance Pretty Ontology where
    pretty = text . show  -- printOntology

setToDocs :: Pretty a => Set.Set a -> [Doc]
setToDocs = punctuate comma . map pretty . Set.toList

setToDocF :: Pretty a => Set.Set a -> Doc
setToDocF = fsep . setToDocs

setToDocV :: (Pretty a) => Set.Set a -> Doc
setToDocV = vcat . setToDocs
