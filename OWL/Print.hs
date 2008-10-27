{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

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

instance Pretty QName where
    pretty = printURIreference

printURIreference :: QName -> Doc
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
    pretty = text . show

instance Pretty Description where
    pretty = printDescription

cardinalityType :: CardinalityType -> Doc
cardinalityType ty = text $ case ty of
    MinCardinality -> "min"
    MaxCardinality -> "max"
    ExactCardinality -> "exactly"

quantifierType :: QuantifierType -> Doc
quantifierType ty = text $ case ty of
    AllValuesFrom -> "only"
    SomeValuesFrom -> "some"

printDescription :: Description -> Doc
printDescription desc = case desc of
   OWLClass ocUri -> printURIreference ocUri
   ObjectJunction UnionOf descList ->
      text "or:" <+> sepByCommas (setToDocs $ Set.fromList descList)
   ObjectJunction IntersectionOf descList ->
      printDescriptionWithRestriction descList
   ObjectComplementOf d -> text "not" <+> pretty d
   ObjectOneOf indUriList -> specBraces $ setToDocF $ Set.fromList indUriList
   ObjectValuesFrom ty opExp d ->
      printObjPropExp opExp <+> quantifierType ty <+> pretty d
   ObjectExistsSelf opExp ->
      printObjPropExp opExp <+> text "some" <+> text "self"
   ObjectHasValue opExp indUri ->
      pretty opExp <+> text "value" <+> pretty indUri
   ObjectCardinality (Cardinality ty card opExp maybeDesc) ->
      printObjPropExp opExp <+> cardinalityType ty
        <+> text (show card) <+> maybe empty pretty maybeDesc
   DataValuesFrom ty dpExp dpExpList dRange ->
       printURIreference dpExp <+> quantifierType ty
           <+> (if null dpExpList then empty
                 else specBraces (sepByCommas $ setToDocs
                   (Set.fromList dpExpList))) <+> pretty dRange
   DataHasValue dpExp cons -> pretty dpExp <+> text "value" <+> pretty cons
   DataCardinality (Cardinality ty card dpExp maybeRange) ->
       pretty dpExp <+> cardinalityType ty <+> text (show card)
         <+> maybe empty pretty maybeRange

printDescriptionWithRestriction :: [Description] -> Doc
printDescriptionWithRestriction descList =
    writeDesc descList True False empty
  where
    writeDesc [] _ _ doc = doc
    writeDesc (h : r) isFirst lastWasNamed doc =
     let thisIsNamed = (case h of
                         OWLClass _ -> True
                         _ -> False)
     in writeDesc r False thisIsNamed $ if isFirst then printDescription h else
          if not lastWasNamed then doc $+$ text "and" <+> printDescription h
          else (case h of
                       OWLClass _ -> doc $+$ text "and"
                       ObjectJunction _ _ -> doc $+$ text "and"
                       ObjectComplementOf _ -> doc $+$ text "and"
                       ObjectOneOf _ -> doc $+$ text "and"
                       _ -> doc $+$ text "that") <+> printDescription h

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
    pretty (Constant lexi ty) = text lexi <> case ty of
      Typed u -> text "^^" <> pretty u
      Untyped tag -> text "@@" <> text tag -- really two "@@" ?

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
  EntityAnno _ -> empty -- EntityAnnotation
  PlainAxiom _ paxiom -> case paxiom of
   SubClassOf sub super ->
       classStart <+> pretty sub $+$ (text "SubClassOf:") $+$
                   (pretty super)
   EquivalentClasses (clazz:equiList) ->
       classStart <+> pretty clazz $+$ (text "EquivalentTo:") $+$
                      (setToDocV $ Set.fromList equiList)

   DisjointClasses (clazz:equiList) ->
       classStart <+> pretty clazz $+$ (text "DisjointWith:") $+$
                   (setToDocV $ Set.fromList equiList)
   DisjointUnion curi discList ->
       classStart <+> pretty curi $+$ (text "DisjointUnionOf:") $+$
                   (setToDocV $ Set.fromList discList)
   -- ObjectPropertyAxiom
   SubObjectPropertyOf sopExp opExp ->
       opStart <+> pretty sopExp $+$ (text "SubObjectPropertyOf:") $+$
                (pretty opExp)
   EquivalentObjectProperties (opExp:opList) ->
       opStart <+> pretty opExp $+$ (text "EquivalentTo:") $+$
                   (setToDocV $ Set.fromList opList)
   DisjointObjectProperties (opExp:opList) ->
       opStart <+> pretty opExp $+$ (text "DisjointWith:") $+$
                   (setToDocV $ Set.fromList opList)
   ObjectPropertyDomain opExp desc ->
       opStart <+> pretty opExp $+$ (text "Domain:") $+$
                   (pretty desc)
   ObjectPropertyRange opExp desc ->
       opStart <+> pretty opExp $+$ (text "Range:") $+$
                   (pretty desc)
   InverseObjectProperties opExp1 opExp2 ->
       opStart <+> pretty opExp1 $+$ (text "Inverse:") $+$
                   (pretty opExp2)
   FunctionalObjectProperty opExp ->
       opStart <+> pretty opExp $+$ (printCharact "Functinal")
   InverseFunctionalObjectProperty opExp ->
       opStart <+> pretty opExp $+$ (printCharact "Inverse_Functinal")
   ReflexiveObjectProperty opExp ->
       opStart <+> pretty opExp $+$ (printCharact "Reflexive")
   IrreflexiveObjectProperty opExp ->
       opStart <+> pretty opExp $+$ (printCharact "Irreflexive")
   SymmetricObjectProperty opExp ->
       opStart <+> pretty opExp $+$ (printCharact "Symmetric")
   AntisymmetricObjectProperty opExp ->
       opStart <+> pretty opExp $+$ (printCharact "AntiSymmetric")
   TransitiveObjectProperty opExp ->
       opStart <+> pretty opExp $+$ (printCharact "Transitive")
   -- DataPropertyAxiom
   SubDataPropertyOf dpExp1 dpExp2 ->
       dpStart <+> pretty dpExp1 $+$ (text "SubDataPropertyOf") $+$
                (pretty dpExp2)
   EquivalentDataProperties (dpExp:dpList) ->
       opStart <+> pretty dpExp $+$ (text "EquivalentTo:") $+$
                (setToDocV $ Set.fromList dpList)
   DisjointDataProperties (dpExp:dpList) ->
       opStart <+> pretty dpExp $+$ (text "DisjointWith:") $+$
                   (setToDocV $ Set.fromList dpList)
   DataPropertyDomain dpExp desc ->
       opStart <+> pretty dpExp $+$ (text "Domain:") $+$
                   (pretty desc)
   DataPropertyRange dpExp desc ->
       opStart <+> pretty dpExp $+$ (text "Range:") $+$
                   (pretty desc)
   FunctionalDataProperty dpExp ->
       opStart <+> pretty dpExp $+$ (printCharact "Functinal")
   -- Fact
   SameIndividual (ind:indList) ->
       indStart <+> (pretty ind) $+$ (text "SameAs:") $+$
                 (setToDocV $ Set.fromList indList)
   DifferentIndividuals (ind:indList) ->
       indStart <+> (pretty ind) $+$ (text "DifferentFrom:") $+$
                 (setToDocV $ Set.fromList indList)
   ClassAssertion ind desc ->
       indStart <+> (pretty ind) $+$ (text "Types:") $+$
                 (pretty desc)
   ObjectPropertyAssertion opExp source target ->
       indStart <+> (pretty source) $+$ (pretty opExp) $+$
                 (pretty target)
   NegativeObjectPropertyAssertion opExp source target ->
       indStart <+> (pretty source) $+$ (text "not" <+>
                                  parens (pretty opExp <+> pretty target))
   DataPropertyAssertion dpExp source target ->
       indStart <+> (pretty source) $+$ (pretty dpExp) $+$
                 (pretty target)
   NegativeDataPropertyAssertion dpExp source target ->
       indStart <+> (pretty source) $+$ (text "not" <+>
                                  parens (pretty dpExp <+> pretty target))
   Declaration _ -> empty    -- [Annotation] Entity
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
    text "Characteristics:" $+$ (text charact)

instance Pretty SubObjectPropertyExpression where
    pretty sopExp =
        case sopExp of
          OPExpression opExp -> pretty opExp
          SubObjectPropertyChain opExpList ->
              foldl (\x y -> x <+> text "o" <+> y)
                  empty (setToDocs (Set.fromList $
                                 take (length opExpList -1) opExpList)) <+>
                  text "o" <+> pretty (head $ reverse opExpList)

instance Pretty OntologyFile where
    pretty = text . show

setToDocs :: Pretty a => Set.Set a -> [Doc]
setToDocs = punctuate comma . map pretty . Set.toList

setToDocF :: Pretty a => Set.Set a -> Doc
setToDocF = fsep . setToDocs

setToDocV :: (Pretty a) => Set.Set a -> Doc
setToDocV = vcat . setToDocs
