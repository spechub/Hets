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
cardinalityType = text . showCardinalityType

quantifierType :: QuantifierType -> Doc
quantifierType = text . showQuantifierType

printDescription :: Description -> Doc
printDescription desc = case desc of
   OWLClass ocUri -> printURIreference ocUri
   ObjectJunction UnionOf descList ->
      fsep $ punctuate (text "or") (setToDocs $ Set.fromList descList)
   ObjectJunction IntersectionOf descList ->
      printDescriptionWithRestriction descList
   ObjectComplementOf d -> text "not" <+> pretty d
   ObjectOneOf indUriList -> specBraces $ setToDocF $ Set.fromList indUriList
   ObjectValuesFrom ty opExp d ->
      printObjPropExp opExp <+> quantifierType ty <+> pretty d
   ObjectExistsSelf opExp ->
      printObjPropExp opExp <+> text "Self"
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
    OWLFact fact -> pretty fact

instance Pretty Axiom where
    pretty = printAxiom

printEquivOrDisjoint :: EquivOrDisjoint -> Doc
printEquivOrDisjoint = text . showEquivOrDisjoint

printObjDomainOrRange :: ObjDomainOrRange -> Doc
printObjDomainOrRange = text . showObjDomainOrRange

printDataDomainOrRange :: DataDomainOrRange -> Doc
printDataDomainOrRange dr = case dr of
    DataDomain d -> text "Domain:" $+$ pretty d
    DataRange d -> text "Range:" $+$ pretty d

printSameOrDifferent :: SameOrDifferent -> Doc
printSameOrDifferent = text . showSameOrDifferent

printAssertion :: (Pretty a, Pretty b) => Assertion a b -> Doc
printAssertion (Assertion a p s b) = indStart <+> pretty s $+$
   let d = pretty a $+$ pretty b in
   case p of
     Positive -> d
     Negative -> text "not" <+> parens d

printAxiom :: Axiom -> Doc
printAxiom axiom = case axiom of
  EntityAnno _ -> empty -- EntityAnnotation
  PlainAxiom _ paxiom -> case paxiom of
   SubClassOf sub super ->
       classStart <+> pretty sub $+$ (text "SubClassOf:") $+$ pretty super
   EquivOrDisjointClasses ty (clazz : equiList) ->
       classStart <+> pretty clazz $+$ printEquivOrDisjoint ty $+$
                      setToDocV (Set.fromList equiList)
   DisjointUnion curi discList ->
       classStart <+> pretty curi $+$ text "DisjointUnionOf:" $+$
                   setToDocV (Set.fromList discList)
   -- ObjectPropertyAxiom
   SubObjectPropertyOf sopExp opExp ->
       opStart <+> pretty sopExp $+$ text "SubObjectPropertyOf:"
                   $+$ pretty opExp
   EquivOrDisjointObjectProperties ty (opExp : opList) ->
       opStart <+> pretty opExp $+$ printEquivOrDisjoint ty $+$
                   setToDocV (Set.fromList opList)
   ObjectPropertyDomainOrRange ty opExp desc ->
       opStart <+> pretty opExp $+$ printObjDomainOrRange ty $+$ pretty desc
   InverseObjectProperties opExp1 opExp2 ->
       opStart <+> pretty opExp1 $+$ text "Inverse:" $+$ pretty opExp2
   ObjectPropertyCharacter ch opExp ->
       opStart <+> pretty opExp $+$ printCharact (show ch)
   -- DataPropertyAxiom
   SubDataPropertyOf dpExp1 dpExp2 ->
       dpStart <+> pretty dpExp1 $+$ text "SubDataPropertyOf" $+$ pretty dpExp2
   EquivOrDisjointDataProperties ty (dpExp : dpList) ->
       dpStart <+> pretty dpExp $+$ printEquivOrDisjoint ty $+$
               setToDocV (Set.fromList dpList)
   DataPropertyDomainOrRange ddr dpExp ->
       dpStart <+> pretty dpExp $+$ printDataDomainOrRange ddr
   FunctionalDataProperty dpExp ->
       dpStart <+> pretty dpExp $+$ (printCharact "Functional")
   -- Fact
   SameOrDifferentIndividual ty (ind : indList) ->
       indStart <+> pretty ind $+$ printSameOrDifferent ty $+$
                 setToDocV (Set.fromList indList)
   ClassAssertion ind desc ->
       indStart <+> pretty ind $+$ text "Types:" $+$ pretty desc
   ObjectPropertyAssertion ass -> printAssertion ass
   DataPropertyAssertion ass -> printAssertion ass
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
