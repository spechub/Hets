{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2005-2006
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Pretty printing for OWL DL theories.
-}

module OWL.Print (printOWLBasicTheory, printAxiom) where

import Common.AS_Annotation
import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Keywords

import OWL.AS
import OWL.Keywords
import OWL.ColonKeywords
import OWL.Sign

import qualified Data.Set as Set
import qualified Data.Map as Map

printOWLBasicTheory :: (Sign, [Named Axiom]) -> Doc
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
       ts = Set.filter ((`notElem` datatypeKeys) . localPart) $ datatypes s
       on = ontologyID s
       pon = printURIreference $ if on == nullQName
             then dummyQName
             else on
   in vcat (map (\ (c, l) -> hsep $ map text
                 [namespaceC, c, '<' : l ++ ">"]
                 -- [prefixC, c ++ ":", '<' : l ++ ">"]
                ) $ Map.toList $ namespaceMap s) $++$
   text ontologyC <+> pon $++$ -- comment out this line for API v3
   vcat (map (\ t -> text datatypeC <+> pretty t) $ Set.toList ts)
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

instance Pretty SymbItems where
  pretty (SymbItems m us) = maybe empty (keyword . show) m
    <+> ppWithCommas us

instance Pretty SymbMapItems where
  pretty (SymbMapItems m us) = maybe empty (keyword . show) m
    <+> sepByCommas
        (map (\ (s, ms) -> sep
              [ pretty s
              , case ms of
                  Nothing -> empty
                  Just t -> mapsto <+> pretty t]) us)

instance GetRange RawSymb -- no position by default

instance Pretty RawSymb where
  pretty rs = case rs of
    ASymbol e -> pretty e
    AnUri u -> pretty u

instance Pretty Entity where
  pretty (Entity ty e) = keyword (show ty) <+> pretty e

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
          UnionOf -> (orS, pretty)
          IntersectionOf -> (andS, printPrimary)
      in fsep $ prepPunctuate (text k <> space) $ map p ds
   ObjectComplementOf d -> text notS <+> printNegatedPrimary d
   ObjectOneOf indUriList -> specBraces $ ppWithCommas indUriList
   ObjectValuesFrom ty opExp d ->
      printObjPropExp opExp <+> quantifierType ty <+> printNegatedPrimary d
   ObjectExistsSelf opExp ->
      printObjPropExp opExp <+> text selfS
   ObjectHasValue opExp indUri ->
      pretty opExp <+> text valueS <+> pretty indUri
   ObjectCardinality (Cardinality ty card opExp maybeDesc) ->
      printObjPropExp opExp <+> cardinalityType ty
        <+> text (show card) <+> maybe (text "owl:Thing") printPrimary maybeDesc
   DataValuesFrom ty dpExp dpExpList dRange ->
       printURIreference dpExp <+> quantifierType ty
           <+> (if null dpExpList then empty
                 else specBraces $ ppWithCommas dpExpList) <+> pretty dRange
   DataHasValue dpExp cons -> pretty dpExp <+> text valueS <+> pretty cons
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
  ObjectHasValue _ _ -> r
  DataHasValue _ _ -> r
  _ -> printPrimary d

instance Pretty ObjectPropertyExpression where
    pretty = printObjPropExp

printObjPropExp :: ObjectPropertyExpression -> Doc
printObjPropExp obExp =
    case obExp of
     OpURI ou -> pretty ou
     InverseOp iopExp -> text inverseS <+> printObjPropExp iopExp

instance Pretty DataRange where
    pretty = printDataRange

printDataRange :: DataRange -> Doc
printDataRange dr = case dr of
    DRDatatype du -> pretty du
    DataComplementOf drange -> text notS <+> pretty drange
    DataOneOf constList -> specBraces $ ppWithCommas constList
    DatatypeRestriction drange l -> pretty drange <+>
      if null l then empty else brackets $ sepByCommas $ map printFV l

printFV :: (DatatypeFacet, RestrictionValue) -> Doc
printFV (facet, restValue) = pretty facet <+> pretty restValue

instance Pretty DatatypeFacet where
    pretty = text . showFacet

instance Pretty Constant where
    pretty (Constant lexi ty) =
     text (case lexi of
             '"' : _ -> lexi
             _ -> show lexi) <> case ty of
      Typed u -> text cTypeS <> pretty u
      Untyped tag -> if null tag then empty else text asP <> text tag

instance Pretty Axiom where
    pretty = printAxiom

printEquivOrDisjoint :: EquivOrDisjoint -> Doc
printEquivOrDisjoint = text . showEquivOrDisjoint

printObjDomainOrRange :: ObjDomainOrRange -> Doc
printObjDomainOrRange = text . showObjDomainOrRange

printDataDomainOrRange :: DataDomainOrRange -> Doc
printDataDomainOrRange dr = case dr of
    DataDomain d -> text domainC <+> pretty d
    DataRange d -> text rangeC <+> pretty d

printSameOrDifferent :: SameOrDifferent -> Doc
printSameOrDifferent = text . showSameOrDifferent

printAssertion :: (Pretty a, Pretty b) => Assertion a b -> Doc
printAssertion (Assertion a p s b) = indStart <+> pretty s $+$
   let d = fsep [pretty a, pretty b] in
   text factsC <+> case p of
     Positive -> d
     Negative -> text notS <+> d

printAxiom :: Axiom -> Doc
printAxiom axiom = case axiom of
  EntityAnno _ -> empty -- EntityAnnotation
  PlainAxiom _ paxiom -> case paxiom of
   SubClassOf sub super -> case super of
     OWLClassDescription curi
       | localPart curi == "Thing" && namePrefix curi == "owl" -> empty
     _ -> classStart <+> pretty sub $+$ text subClassOfC <+> pretty super
   EquivOrDisjointClasses ty (clazz : equiList) ->
       classStart <+> pretty clazz $+$ printEquivOrDisjoint ty <+>
                      setToDocV (Set.fromList equiList)
   DisjointUnion curi discList ->
       classStart <+> pretty curi $+$ text disjointUnionOfC <+>
                   setToDocV (Set.fromList discList)
   -- ObjectPropertyAxiom
   SubObjectPropertyOf sopExp opExp ->
       opStart <+> pretty opExp $+$ text (case sopExp of
                 SubObjectPropertyChain _ -> subPropertyChainC
                 _ -> subPropertyOfC)
                   <+> pretty sopExp
   EquivOrDisjointObjectProperties ty (opExp : opList) ->
       opStart <+> pretty opExp $+$ printEquivOrDisjoint ty <+>
                   setToDocV (Set.fromList opList)
   ObjectPropertyDomainOrRange ty opExp desc ->
       opStart <+> pretty opExp $+$ printObjDomainOrRange ty <+> pretty desc
   InverseObjectProperties opExp1 opExp2 ->
       opStart <+> pretty opExp1 $+$ text inverseOfC <+> pretty opExp2
   ObjectPropertyCharacter ch opExp ->
       opStart <+> pretty opExp $+$ printCharact (show ch)
   -- DataPropertyAxiom
   SubDataPropertyOf dpExp1 dpExp2 ->
       dpStart <+> pretty dpExp1 $+$ text subPropertyOfC <+> pretty dpExp2
   EquivOrDisjointDataProperties ty (dpExp : dpList) ->
       dpStart <+> pretty dpExp $+$ printEquivOrDisjoint ty <+>
               setToDocV (Set.fromList dpList)
   DataPropertyDomainOrRange ddr dpExp ->
       dpStart <+> pretty dpExp $+$ printDataDomainOrRange ddr
   FunctionalDataProperty dpExp ->
       dpStart <+> pretty dpExp $+$ printCharact functionalS
   -- Fact
   SameOrDifferentIndividual ty (ind : indList) ->
       indStart <+> pretty ind $+$ printSameOrDifferent ty <+>
                 setToDocV (Set.fromList indList)
   ClassAssertion ind desc ->
       indStart <+> pretty ind $+$ text typesC <+> pretty desc
   ObjectPropertyAssertion ass -> printAssertion ass
   DataPropertyAssertion ass -> printAssertion ass
   Declaration _ -> empty    -- [Annotation] Entity
   u -> error $ "unknow axiom " ++ show u

classStart :: Doc
classStart = text classC

opStart :: Doc
opStart = text objectPropertyC

dpStart :: Doc
dpStart = text dataPropertyC

indStart :: Doc
indStart = text individualC

printCharact :: String -> Doc
printCharact charact =
    text characteristicsC <+> text charact

instance Pretty SubObjectPropertyExpression where
    pretty sopExp =
        case sopExp of
          OPExpression opExp -> pretty opExp
          SubObjectPropertyChain opExpList ->
             fsep $ prepPunctuate (text oS <> space) $ map pretty opExpList

instance Pretty OntologyFile where
    pretty = vsep . map pretty . axiomsList . ontology

setToDocs :: Pretty a => Set.Set a -> [Doc]
setToDocs = punctuate comma . map pretty . Set.toList

setToDocV :: (Pretty a) => Set.Set a -> Doc
setToDocV = vcat . setToDocs
