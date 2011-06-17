{- |
Module      :  $Header$
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Pretty printing for OWL2 - Manchester syntax
-}

module OWL2.ManchesterPrint where

import Common.Doc
import Common.DocUtils
import Common.Keywords

import OWL2.AS
import OWL2.MS
import OWL2.Print
import OWL.Keywords
import OWL.ColonKeywords

--import qualified Data.Set as Set

printCharact :: String -> Doc
printCharact charact = text charact

instance Pretty Character where
  pretty = printCharact . show 

instance Pretty AnnotationValue where
    pretty x = case x of
      AnnValue iri -> pretty iri
      AnnValLit lit -> pretty lit 

instance Pretty Annotation where
    pretty = printAnnotation

printAnnotation :: Annotation -> Doc
printAnnotation (Annotation _ ap av) = pretty ap <+> pretty av 

instance Pretty Annotations where
    pretty = printAnnotations

printAnnotations :: Annotations -> Doc
printAnnotations (Annotations l) = case l of
    [] -> empty
    _ -> keyword annotationsC <+> vcat ( punctuate comma (map ( \(ans, a) -> pretty ans $+$ pretty a) l ) )

instance Pretty a => Pretty (AnnotatedList a) where
    pretty = printAnnotatedList
    
printAnnotatedList :: Pretty a => AnnotatedList a -> Doc
printAnnotatedList (AnnotatedList l) = vcat ( punctuate comma $ map ( \(ans, a) -> pretty ans $+$ pretty a) l )
  
instance Pretty ClassFrameBit where
    pretty = printClassFrameBit

printClassFrameBit :: ClassFrameBit -> Doc
printClassFrameBit cfb = case cfb of
    ClassAnnotations x -> pretty x
    ClassSubClassOf x -> keyword subClassOfC <+> pretty x
    ClassEquivOrDisjoint x y -> printEquivOrDisjoint x <+> pretty y
    ClassDisjointUnion a x -> keyword disjointUnionOfC <+> (pretty a $+$ vcat(punctuate comma ( map (\p -> pretty p) x )))
    ClassHasKey a op dp -> keyword hasKeyC <+> (pretty a
      $+$ vcat (punctuate comma $ map pretty op ++ map pretty dp))

instance Pretty ObjectFrameBit where
    pretty = printObjectFrameBit

printObjectFrameBit :: ObjectFrameBit -> Doc
printObjectFrameBit ofb = case ofb of
    ObjectAnnotations x -> pretty x
    ObjectDomainOrRange dr x -> printObjDomainOrRange dr <+> pretty x
    ObjectCharacteristics x -> keyword characteristicsC <+> pretty x
    ObjectEquivOrDisjoint ed x -> printEquivOrDisjoint ed <+> pretty x
    ObjectInverse x -> keyword inverseOfC <+> pretty x
    ObjectSubPropertyChain a opl -> keyword subPropertyChainC <+> (pretty a $+$ fsep (prepPunctuate (keyword oS <> space) $ map pretty opl))
    ObjectSubPropertyOf x -> keyword subPropertyOfC <+> pretty x

instance Pretty DataFrameBit where
    pretty = printDataFrameBit

printDataFrameBit :: DataFrameBit -> Doc
printDataFrameBit dfb = case dfb of
    DataAnnotations x -> pretty x
    DataPropDomain x -> keyword domainC <+> pretty x
    DataPropRange x -> keyword rangeC <+> pretty x 
    DataFunctional x -> keyword characteristicsC <+> (pretty x $+$ printCharact functionalS) 
    DataSubPropertyOf x -> keyword subPropertyOfC <+> pretty x
    DataEquivOrDisjoint e x -> printEquivOrDisjoint e <+> pretty x

instance Pretty IndividualBit where
    pretty = printIndividualBit

printIndividualBit :: IndividualBit -> Doc
printIndividualBit ib = case ib of
    IndividualAnnotations x -> pretty x
    IndividualTypes x -> keyword typesC <+> pretty x
    IndividualFacts x -> keyword factsC <+> pretty x
    IndividualSameOrDifferent s x -> printSameOrDifferent s <+> pretty x

instance Pretty Fact where
    pretty = printFact

printFact :: Fact -> Doc
printFact pf = case pf of
    ObjectPropertyFact pn op i -> printPositiveOrNegative pn <+> pretty op <+> pretty i
    DataPropertyFact pn dp l -> printPositiveOrNegative pn <+> pretty dp <+> pretty l

printPositiveOrNegative :: PositiveOrNegative -> Doc
printPositiveOrNegative x = case x of
    Positive -> empty
    Negative -> keyword notS

instance Pretty AnnotationBit where
    pretty = printAnnotationBit

printAnnotationBit :: AnnotationBit -> Doc
printAnnotationBit ab = case ab of
    AnnotationAnnotations x -> pretty x
    AnnotationDOR dor x -> printAnnDomainOrRange dor <+> pretty x
    AnnotationSubPropertyOf x -> keyword subPropertyOfC <+> pretty x

printAnnDomainOrRange :: AnnotationDomainOrRange -> Doc
printAnnDomainOrRange = keyword . showAnnDomainOrRange

instance Pretty Frame where
    pretty = printFrame

printMaybeAnnDR :: Maybe (Annotations, DataRange) -> Doc
printMaybeAnnDR x = case x of
    Nothing -> empty
    Just (a, dr) -> keyword equivalentToC <+> (pretty a $+$ pretty dr) 

printFrame :: Frame -> Doc
printFrame x = case x of
    ClassFrame a cfb -> classStart <+> pretty a <+> vcat (map pretty cfb)
    DatatypeFrame d ans a ans2 -> keyword datatypeC <+> (pretty d $+$ vcat (map pretty ans) $+$ printMaybeAnnDR a $+$ vcat (map pretty ans2))
    ObjectPropertyFrame op ofb -> keyword objectPropertyC <+> pretty op <+> vcat (map pretty ofb)
    DataPropertyFrame dp dfb -> keyword dataPropertyC <+> pretty dp <+> vcat (map pretty dfb)
    IndividualFrame i ib -> keyword individualC <+> pretty i <+> vcat (map pretty ib)
    AnnotationFrame ap ab -> keyword annotationPropertyC <+> pretty ap  <+> vcat (map pretty ab)
    MiscEquivOrDisjointClasses e a c -> printEquivOrDisjointClasses e <+> (pretty a $+$ vcat (punctuate comma (map pretty c) ))
    MiscEquivOrDisjointObjProp e a c -> printEquivOrDisjointObj e <+> (pretty a $+$ vcat ( punctuate comma (map pretty c) ))
    MiscEquivOrDisjointDataProp e a c -> printEquivOrDisjointData e <+> (pretty a $+$ vcat ( punctuate comma (map pretty c) ))
    MiscSameOrDifferent s a c -> printSameOrDifferentInd s <+> (pretty a $+$ vcat( punctuate comma (map pretty c) ))

printEquivOrDisjointClasses :: EquivOrDisjoint -> Doc
printEquivOrDisjointClasses x = case x of
    Equivalent -> text "EquivalentClasses:"
    Disjoint -> text "DisjointClasses:"

printEquivOrDisjointObj :: EquivOrDisjoint -> Doc
printEquivOrDisjointObj x = case x of
    Equivalent -> text "EquivalentProperties:"
    Disjoint -> text "DisjointProperties:"

printEquivOrDisjointData :: EquivOrDisjoint -> Doc
printEquivOrDisjointData x = case x of
    Equivalent -> text "EquivalentProperties:"
    Disjoint -> text "DisjointProperties:"

printSameOrDifferentInd :: SameOrDifferent -> Doc
printSameOrDifferentInd x = case x of
    Same -> keyword sameIndividualC
    Different -> keyword differentIndividualsC

instance Pretty OntologyDocument where
    pretty = vsep . map pretty . ontologyFrame . mOntology
