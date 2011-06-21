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
  
instance Pretty FrameBit where
    pretty = printFrameBit

printFrameBit :: FrameBit -> Doc
printFrameBit fb = case fb of
    AnnotationFrameBit x -> pretty x
    AnnotationBit ed l -> printEquivOrDisjoint ed <+> pretty l
    DatatypeBit ans a -> pretty ans $+$ pretty a
    ExpressionBit x y -> printEquivOrDisjoint x <+> pretty y
    ClassDisjointUnion a x -> keyword disjointUnionOfC 
      <+> (pretty a $+$ vcat(punctuate comma ( map (\p -> pretty p) x )))
    ClassHasKey a op dp -> keyword hasKeyC <+> (pretty a
      $+$ vcat (punctuate comma $ map pretty op ++ map pretty dp))
    ObjectBit dr x -> printEquivOrDisjoint dr <+> pretty x
    ObjectCharacteristics x -> keyword characteristicsC <+> pretty x
    ObjectSubPropertyChain a opl -> keyword subPropertyChainC 
      <+> (pretty a $+$ fsep (prepPunctuate (keyword oS <> space) $ map pretty opl))
    DataBit dr x -> printEquivOrDisjoint dr <+> pretty x
    DataPropRange x -> keyword rangeC <+> pretty x 
    DataFunctional x -> keyword characteristicsC <+> (pretty x $+$ printCharact functionalS) 
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

instance Pretty Frame where
    pretty = printFrame

instance Pretty Misc where
    pretty = printMisc

printMisc :: Misc -> Doc
printMisc m = case m of 
    MiscEquivOrDisjointClasses e a c -> printEquivOrDisjointClasses e <+> (pretty a $+$ vcat (punctuate comma (map pretty c) ))
    MiscEquivOrDisjointObjProp e a c -> printEquivOrDisjointObj e <+> (pretty a $+$ vcat ( punctuate comma (map pretty c) ))
    MiscEquivOrDisjointDataProp e a c -> printEquivOrDisjointData e <+> (pretty a $+$ vcat ( punctuate comma (map pretty c) ))
    MiscSameOrDifferent s a c -> printSameOrDifferentInd s <+> (pretty a $+$ vcat( punctuate comma (map pretty c) ))

printFrame :: Frame -> Doc
printFrame f = case f of
    Frame (Entity e uri) bl -> pretty (showEntityType e) <+> pretty uri <+> vcat (map pretty bl)
    MiscFrame misc -> pretty misc

printEquivOrDisjointClasses :: EquivOrDisjoint -> Doc
printEquivOrDisjointClasses x = case x of
    Equivalent -> text "EquivalentClasses:"
    Disjoint -> text "DisjointClasses:"
    _ -> empty

printEquivOrDisjointObj :: EquivOrDisjoint -> Doc
printEquivOrDisjointObj x = case x of
    Equivalent -> text "EquivalentProperties:"
    Disjoint -> text "DisjointProperties:"
    _ -> empty

printEquivOrDisjointData :: EquivOrDisjoint -> Doc
printEquivOrDisjointData x = case x of
    Equivalent -> text "EquivalentProperties:"
    Disjoint -> text "DisjointProperties:"
    _ -> empty

printSameOrDifferentInd :: SameOrDifferent -> Doc
printSameOrDifferentInd x = case x of
    Same -> keyword sameIndividualC
    Different -> keyword differentIndividualsC
    Individuals -> keyword individualsC

instance Pretty MOntology where
    pretty = printOntology

printImport :: ImportIRI -> Doc
printImport x = keyword importC <+> pretty x 

printOntology :: MOntology -> Doc
printOntology MOntology {muri = a, imports = b, ann = c, ontologyFrame = d} = keyword ontologyC <+> pretty a $+$ vcat (map printImport b) $+$ vcat (map pretty c) $+$ vcat(map pretty d) 

instance Pretty OntologyDocument where
    pretty = pretty . mOntology
