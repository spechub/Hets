{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2005-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Contains    :  Pretty Printing for the Functional Syntax of OWL 2
-}

module OWL2.FunctionalPrint where

import Common.Doc
import Common.DocUtils
import Common.Keywords
import Common.AS_Annotation

import OWL2.AS
import OWL2.FS
import OWL2.Print
import OWL2.Keywords
import OWL2.ColonKeywords
import OWL2.Sign

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
       ts = Set.filter ((`notElem` datatypeKeys) . localPart) $ datatypes s
   in vcat (map (\ (c, l) -> hsep $ map text
                 [namespaceC, c, '<' : l ++ ">"]
                 -- [prefixC, c ++ ":", '<' : l ++ ">"]
                ) $ Map.toList $ prefixMap s) $++$
   vcat (map (\ t -> keyword datatypeC <+> pretty t) $ Set.toList ts)
   $++$ vcat (map (\ c -> keyword classC <+> pretty c) $ Set.toList cs)
   $++$ vcat (map (\ o -> keyword objectPropertyC <+> pretty o) $ Set.toList $ objectProperties s)
   $++$
     vcat (map (\ d -> keyword dataPropertyC <+> pretty d) $ Set.toList $ dataProperties s)
   $++$ vcat (map (\ i -> keyword individualC <+> pretty i) $ Set.toList $ individuals s)
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

instance Pretty Axiom where
    pretty = printAxiom

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
   EquivOrDisjointClasses ty equiList ->
       printEquivOrDisjointClasses ty <+> setToDocV (Set.fromList equiList)
   DisjointUnion curi discList ->
       classStart <+> pretty curi $+$ keyword disjointUnionOfC <+>
                   setToDocV (Set.fromList discList)
   -- ObjectPropertyAxiom
   SubObjectPropertyOf sopExp opExp ->
       opStart <+> pretty opExp $+$ keyword (case sopExp of
                 SubObjectPropertyChain _ -> subPropertyChainC
                 _ -> subPropertyOfC)
                   <+> pretty sopExp
   EquivOrDisjointObjectProperties ty opList ->
       printEquivOrDisjointObj ty <+> setToDocV (Set.fromList opList)
   ObjectPropertyDomainOrRange ty opExp desc ->
       opStart <+> pretty opExp $+$ printDomainOrRange ty <+> pretty desc
   InverseObjectProperties opExp1 opExp2 ->
       opStart <+> pretty opExp1 $+$ keyword inverseOfC <+> pretty opExp2
   ObjectPropertyCharacter ch opExp ->
       opStart <+> pretty opExp $+$ printCharact (show ch)
   -- DataPropertyAxiom
   SubDataPropertyOf dpExp1 dpExp2 ->
       dpStart <+> pretty dpExp1 $+$ keyword subPropertyOfC <+> pretty dpExp2
   EquivOrDisjointDataProperties ty dpList ->
       printEquivOrDisjointData ty <+> setToDocV (Set.fromList dpList)
   DataPropertyDomainOrRange ddr dpExp ->
       dpStart <+> pretty dpExp $+$ printDataDomainOrRange ddr
   FunctionalDataProperty dpExp ->
       dpStart <+> pretty dpExp $+$ printCharact functionalS
   -- Fact
   SameOrDifferentIndividual ty (ind : indList) ->
      {-case ty of 
        Individuals -> -}printSameOrDifferentInd ty <+> setToDocV (Set.fromList (ind : indList))
        {-_ -> indStart <+> pretty ind $+$ printSameOrDifferentInd ty <+> 
                 setToDocV (Set.fromList indList)-}
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
