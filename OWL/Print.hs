{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Pretty printing for OWL DL theories.
-}

module OWL.Print (printOWLBasicTheory, printAxiom) where

import Common.AS_Annotation
import Common.Doc
import Common.DocUtils

import OWL.Sign
import OWL.AS

import qualified Data.Set as Set
import qualified Data.Map as Map

printOWLBasicTheory :: (Sign, [Named Sentence]) -> Doc
printOWLBasicTheory (s, l) =
  printSign s
  $++$ vsep (map (pretty . sentence) l)

instance Pretty Sign where
    pretty = printSign

printSign :: Sign -> Doc
printSign s =
   let cs = concepts s
       ps = primaryConcepts s
       ds = Set.difference cs ps
       on = ontologyID s
       pon = if on == nullQName
             then text "<http://www.dfki.de/sks/hets/ontology/unamed>"
             else printURIreference on
   in vcat (map (\ (c, l) -> text $ "Namespace: " ++ c ++ " <" ++ l ++">")
           $ Map.toList $ namespaceMap s)
   $++$ text "Ontology:" <+> pon
   $++$ vcat (map (\ d -> text "Annotations: data"
                   <+> printEntity (Entity Datatype d))
             $ Set.toList $ datatypes s)
   $++$ vcat (map (\ c -> classStart <+> pretty c) $ Set.toList ps)
   $++$ vcat (map (\ c -> classStart <+> pretty c) $ Set.toList ds)
   $++$ vcat (map (\ o -> opStart <+> pretty o) $ Set.toList $ indValuedRoles s)
   $++$
     vcat (map (\ d -> dpStart <+> pretty d) $ Set.toList $ dataValuedRoles s)
   $++$ vcat (map (\ i -> indStart <+> pretty i) $ Set.toList $ individuals s)

instance Pretty QName where
    pretty = printURIreference

printURIreference :: QName -> Doc
printURIreference = text . showQN

instance Pretty SignAxiom where
    pretty = text . show

cardinalityType :: CardinalityType -> Doc
cardinalityType = text . showCardinalityType

quantifierType :: QuantifierType -> Doc
quantifierType = text . showQuantifierType

instance Pretty Description where
  pretty desc = case desc of
   OWLClassDescription ocUri -> printURIreference ocUri
   ObjectJunction ty ds -> let
      (k, p) = case ty of
          UnionOf -> ("or", pretty)
          IntersectionOf -> ("and", printPrimary)
      in fsep $ prepPunctuate (text k <> space) $ map p ds
   ObjectComplementOf d -> text "not" <+> printNegatedPrimary d
   ObjectOneOf indUriList -> specBraces $ ppWithCommas indUriList
   ObjectValuesFrom ty opExp d ->
      printObjPropExp opExp <+> quantifierType ty <+> printNegatedPrimary d
   ObjectExistsSelf opExp ->
      printObjPropExp opExp <+> text "Self"
   ObjectHasValue opExp indUri ->
      pretty opExp <+> text "value" <+> pretty indUri
   ObjectCardinality (Cardinality ty card opExp maybeDesc) ->
      printObjPropExp opExp <+> cardinalityType ty
        <+> text (show card) <+> maybe (text "owl:Thing") printPrimary maybeDesc
   DataValuesFrom ty dpExp dpExpList dRange ->
       printURIreference dpExp <+> quantifierType ty
           <+> (if null dpExpList then empty
                 else specBraces $ ppWithCommas dpExpList) <+> pretty dRange
   DataHasValue dpExp cons -> pretty dpExp <+> text "value" <+> pretty cons
   DataCardinality (Cardinality ty card dpExp maybeRange) ->
       pretty dpExp <+> cardinalityType ty <+> text (show card)
         <+> maybe empty pretty maybeRange

printPrimary :: Description -> Doc
printPrimary d = let dd = pretty d in case d of
  ObjectJunction _ _ -> parens dd
  _ -> dd

printNegatedPrimary :: Description -> Doc
printNegatedPrimary d = let r = parens $ pretty d in case d of
  ObjectComplementOf _ -> r
  ObjectValuesFrom _ _ _ -> r
  DataValuesFrom _ _ _ _ -> r
  _ -> printPrimary d

instance Pretty ObjectPropertyExpression where
    pretty = printObjPropExp

printObjPropExp :: ObjectPropertyExpression -> Doc
printObjPropExp obExp =
    case obExp of
     OpURI ou -> pretty ou
     InverseOp iopExp -> text "inverseOf" <> parens (printObjPropExp iopExp)

instance Pretty DataRange where
    pretty = printDataRange

printDataRange :: DataRange -> Doc
printDataRange dr = case dr of
    DRDatatype du -> pretty du
    DataComplementOf drange -> text "not" <+> pretty drange
    DataOneOf constList -> specBraces $ ppWithCommas constList
    DatatypeRestriction drange l -> pretty drange <+>
      if null l then empty else brackets $ sepByCommas $ map printFV l

printFV :: (DatatypeFacet, RestrictionValue) -> Doc
printFV (facet, restValue) = pretty facet <+> pretty restValue

instance Pretty DatatypeFacet where
    pretty = text . showFacet

instance Pretty Constant where
    pretty (Constant lexi ty) = text lexi <> case ty of
      Typed u -> text "^^" <> pretty u
      Untyped tag -> text "@" <> text tag

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
    DataDomain d -> text "Domain:" <+> pretty d
    DataRange d -> text "Range:" <+> pretty d

printSameOrDifferent :: SameOrDifferent -> Doc
printSameOrDifferent = text . showSameOrDifferent

printAssertion :: (Pretty a, Pretty b) => Assertion a b -> Doc
printAssertion (Assertion a p s b) = indStart <+> pretty s $+$
   let d = fsep [pretty a, pretty b] in
   text "Facts:" <+> case p of
     Positive -> d
     Negative -> text "not" <+> parens d

printEntity :: Entity -> Doc
printEntity (Entity ty u) = text (show ty) <> parens (pretty u)

printAxiom :: Axiom -> Doc
printAxiom axiom = case axiom of
  EntityAnno _ -> empty -- EntityAnnotation
  PlainAxiom _ paxiom -> case paxiom of
   SubClassOf sub super ->
       classStart <+> pretty sub $+$ text "SubClassOf:" <+> pretty super
   EquivOrDisjointClasses ty (clazz : equiList) ->
       classStart <+> pretty clazz $+$ printEquivOrDisjoint ty <+>
                      setToDocV (Set.fromList equiList)
   DisjointUnion curi discList ->
       classStart <+> pretty curi $+$ text "DisjointUnionOf:" <+>
                   setToDocV (Set.fromList discList)
   -- ObjectPropertyAxiom
   SubObjectPropertyOf sopExp opExp ->
       opStart <+> pretty opExp $+$ text (case sopExp of
                 SubObjectPropertyChain _ -> "SubPropertyChain:"
                 _ -> "SubPropertyOf:")
                   <+> pretty sopExp
   EquivOrDisjointObjectProperties ty (opExp : opList) ->
       opStart <+> pretty opExp $+$ printEquivOrDisjoint ty <+>
                   setToDocV (Set.fromList opList)
   ObjectPropertyDomainOrRange ty opExp desc ->
       opStart <+> pretty opExp $+$ printObjDomainOrRange ty <+> pretty desc
   InverseObjectProperties opExp1 opExp2 ->
       opStart <+> pretty opExp1 $+$ text "Inverses:" <+> pretty opExp2
   ObjectPropertyCharacter ch opExp ->
       opStart <+> pretty opExp $+$ printCharact (show ch)
   -- DataPropertyAxiom
   SubDataPropertyOf dpExp1 dpExp2 ->
       dpStart <+> pretty dpExp1 $+$ text "SubPropertyOf" <+> pretty dpExp2
   EquivOrDisjointDataProperties ty (dpExp : dpList) ->
       dpStart <+> pretty dpExp $+$ printEquivOrDisjoint ty <+>
               setToDocV (Set.fromList dpList)
   DataPropertyDomainOrRange ddr dpExp ->
       dpStart <+> pretty dpExp $+$ printDataDomainOrRange ddr
   FunctionalDataProperty dpExp ->
       dpStart <+> pretty dpExp $+$ (printCharact "Functional")
   -- Fact
   SameOrDifferentIndividual ty (ind : indList) ->
       indStart <+> pretty ind $+$ printSameOrDifferent ty <+>
                 setToDocV (Set.fromList indList)
   ClassAssertion ind desc ->
       indStart <+> pretty ind $+$ text "Types:" <+> pretty desc
   ObjectPropertyAssertion ass -> printAssertion ass
   DataPropertyAssertion ass -> printAssertion ass
   Declaration _ -> empty    -- [Annotation] Entity
   u -> error ("unknow axiom" ++ show u)

classStart :: Doc
classStart = text "Class:"

opStart :: Doc
opStart = text "ObjectProperty:"

dpStart :: Doc
dpStart = text "DataProperty:"

indStart :: Doc
indStart = text "Individual:"

printCharact :: String -> Doc
printCharact charact =
    text "Characteristics:" <+> text charact

instance Pretty SubObjectPropertyExpression where
    pretty sopExp =
        case sopExp of
          OPExpression opExp -> pretty opExp
          SubObjectPropertyChain opExpList ->
             fsep $ prepPunctuate (text "o ") $ map pretty opExpList

instance Pretty OntologyFile where
    pretty = vsep . map pretty . axiomsList . ontology

setToDocs :: Pretty a => Set.Set a -> [Doc]
setToDocs = punctuate comma . map pretty . Set.toList

setToDocV :: (Pretty a) => Set.Set a -> Doc
setToDocV = vcat . setToDocs
