{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2005-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Pretty printing for OWL 2 DL theories.
-}

module OWL2.Print ({-printOWLBasicTheory,-} printAxiom) where

import Common.AS_Annotation
import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Keywords

import OWL2.AS
import OWL.Keywords
import OWL.ColonKeywords

import qualified Data.Set as Set
import qualified Data.Map as Map


instance Pretty QName where
    pretty = printURIreference

printURIreference :: QName -> Doc
printURIreference q =
  (if localPart q == "Thing" && elem (namePrefix q) ["", "owl"]
  then keyword else text) $ showQN q

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

cardinalityType :: CardinalityType -> Doc
cardinalityType = keyword . showCardinalityType

quantifierType :: QuantifierType -> Doc
quantifierType = keyword . showQuantifierType

printIndividual :: Individual -> Doc
printIndividual ind = 
    case ind of
      NamedInd n -> pretty n
      AnonymousIndividual a -> pretty a

instance Pretty Individual where
    pretty = printIndividual 

instance Pretty ClassExpression where
  pretty desc = case desc of
   Expression ocUri -> printURIreference ocUri
   ObjectJunction ty ds -> let
      (k, p) = case ty of
          UnionOf -> (orS, pretty)
          IntersectionOf -> (andS, printPrimary)
      in fsep $ prepPunctuate (keyword k <> space) $ map p ds
   ObjectComplementOf d -> keyword notS <+> printNegatedPrimary d
   ObjectOneOf indUriList -> specBraces $ ppWithCommas indUriList
   ObjectValuesFrom ty opExp d ->
      printObjPropExp opExp <+> quantifierType ty <+> printNegatedPrimary d
   ObjectHasSelf opExp ->
      printObjPropExp opExp <+> keyword selfS
   ObjectHasValue opExp indUri ->
      pretty opExp <+> keyword valueS <+> pretty indUri
   ObjectCardinality (Cardinality ty card opExp maybeDesc) ->
      printObjPropExp opExp <+> cardinalityType ty
        <+> text (show card)
        <+> maybe (keyword "owl:Thing") printPrimary maybeDesc
   DataValuesFrom ty dpExp dpExpList dRange ->
       printURIreference dpExp <+> quantifierType ty
           <+> (if null dpExpList then empty
                 else specBraces $ ppWithCommas dpExpList) <+> pretty dRange
   DataHasValue dpExp cons -> pretty dpExp <+> keyword valueS <+> pretty cons
   DataCardinality (Cardinality ty card dpExp maybeRange) ->
       pretty dpExp <+> cardinalityType ty <+> text (show card)
         <+> maybe empty pretty maybeRange

printPrimary :: ClassExpression -> Doc
printPrimary d = let dd = pretty d in case d of
  ObjectJunction _ _ -> parens dd
  _ -> dd

printNegatedPrimary :: ClassExpression -> Doc
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
     ObjectProp ou -> pretty ou
     ObjectInverseOf iopExp -> keyword inverseS <+> printObjPropExp iopExp

instance Pretty DataRange where
    pretty = printDataRange

printDataRange :: DataRange -> Doc
printDataRange dr = case dr of
    DataType du -> pretty du
    DataComplementOf drange -> keyword notS <+> pretty drange
    DataOneOf constList -> specBraces $ ppWithCommas constList
    DatatypeRestriction dtype l -> pretty dtype <+>				
      if null l then empty else brackets $ sepByCommas $ map printFV l
    DataIntersectionOrUnionOf ty drlist -> let
      k = case ty of
          UnionOf -> orS
          IntersectionOf -> andS
      in fsep $ prepPunctuate (keyword k <> space) $ map pretty drlist

printFV ::(ConstrainingFacet, RestrictionValue) -> Doc
printFV (facet, restValue) = pretty facet <+> pretty restValue

instance Pretty DatatypeFacet where
    pretty = keyword . showFacet

instance Pretty Literal where
    pretty (Literal lexi ty) =
     text (case lexi of
             '"' : _ -> lexi
             _ -> show lexi) <> case ty of
      Typed u -> keyword cTypeS <> pretty u
      Untyped tag -> if tag == Nothing then empty else 
                     let Just tag2 = tag in text asP <> text tag2

instance Pretty Axiom where
    pretty = printAxiom

printEquivOrDisjoint :: EquivOrDisjoint -> Doc
printEquivOrDisjoint = keyword . showEquivOrDisjoint

printObjDomainOrRange :: ObjDomainOrRange -> Doc
printObjDomainOrRange = keyword . showObjDomainOrRange

printDataDomainOrRange :: DataDomainOrRange -> Doc
printDataDomainOrRange dr = case dr of
    DataDomain d -> keyword domainC <+> pretty d
    DataRange d -> keyword rangeC <+> pretty d

printSameOrDifferent :: SameOrDifferent -> Doc
printSameOrDifferent = keyword . showSameOrDifferent

printAssertion :: (Pretty a, Pretty b) => Assertion a b -> Doc
printAssertion (Assertion a p s b) = indStart <+> pretty s $+$
   let d = fsep [pretty a, pretty b] in
   keyword factsC <+> case p of
     Positive -> d
     Negative -> keyword notS <+> d

printAxiom :: Axiom -> Doc
printAxiom axiom = case axiom of
  EntityAnno _ -> empty -- EntityAnnotation
  PlainAxiom _ paxiom -> case paxiom of
   SubClassOf sub super -> case super of
     Expression curi
       | localPart curi == "Thing" && namePrefix curi == "owl" -> empty
     _ -> classStart <+> pretty sub $+$ keyword subClassOfC <+> pretty super
   EquivOrDisjointClasses ty (clazz : equiList) ->
       classStart <+> pretty clazz $+$ printEquivOrDisjoint ty <+>
                      setToDocV (Set.fromList equiList)
   DisjointUnion curi discList ->
       classStart <+> pretty curi $+$ keyword disjointUnionOfC <+>
                   setToDocV (Set.fromList discList)
   -- ObjectPropertyAxiom
   SubObjectPropertyOf sopExp opExp ->
       opStart <+> pretty opExp $+$ keyword (case sopExp of
                 SubObjectPropertyChain _ -> subPropertyChainC
                 _ -> subPropertyOfC)
                   <+> pretty sopExp
   EquivOrDisjointObjectProperties ty (opExp : opList) ->
       opStart <+> pretty opExp $+$ printEquivOrDisjoint ty <+>
                   setToDocV (Set.fromList opList)
   ObjectPropertyDomainOrRange ty opExp desc ->
       opStart <+> pretty opExp $+$ printObjDomainOrRange ty <+> pretty desc
   InverseObjectProperties opExp1 opExp2 ->
       opStart <+> pretty opExp1 $+$ keyword inverseOfC <+> pretty opExp2
   ObjectPropertyCharacter ch opExp ->
       opStart <+> pretty opExp $+$ printCharact (show ch)
   -- DataPropertyAxiom
   SubDataPropertyOf dpExp1 dpExp2 ->
       dpStart <+> pretty dpExp1 $+$ keyword subPropertyOfC <+> pretty dpExp2
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
   ClassAssertion desc ind ->
       indStart <+> pretty ind $+$ keyword typesC <+> pretty desc
   ObjectPropertyAssertion ass -> printAssertion ass
   DataPropertyAssertion ass -> printAssertion ass
   Declaration _ -> empty    -- [Annotation] Entity
   DatatypeDefinition dt dr ->
       keyword datatypeC <+> pretty dt $+$ keyword equivalentToC <+> pretty dr
   HasKey cexpr objlist datalist -> classStart <+> pretty cexpr $+$ keyword hasKeyC
     <+> vcat (punctuate comma $ map pretty objlist ++ map pretty datalist)
   u -> error $ "unknow axiom " ++ show u

classStart :: Doc
classStart = keyword classC

opStart :: Doc
opStart = keyword objectPropertyC

dpStart :: Doc
dpStart = keyword dataPropertyC

indStart :: Doc
indStart = keyword individualC

printCharact :: String -> Doc
printCharact charact =
    keyword characteristicsC <+> text charact

instance Pretty SubObjectPropertyExpression where
    pretty sopExp =
        case sopExp of
          OPExpression opExp -> pretty opExp
          SubObjectPropertyChain opExpList ->
             fsep $ prepPunctuate (keyword oS <> space) $ map pretty opExpList

instance Pretty OntologyFile where
    pretty = vsep . map pretty . axiomsList . ontology

setToDocs :: Pretty a => Set.Set a -> [Doc]
setToDocs = punctuate comma . map pretty . Set.toList

setToDocV :: (Pretty a) => Set.Set a -> Doc
setToDocV = vcat . setToDocs
