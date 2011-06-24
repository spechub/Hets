{- |
Module      :  $Header$
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Contains    :  Pretty printing for the Manchester Syntax of OWL 2
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
import qualified Data.Map as Map

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
printAnnotation (Annotation ans ap av) =
  sep [printAnnotations ans, sep [pretty ap, pretty av]]

printAnnotations :: Annotations -> Doc
printAnnotations l = case l of
    [] -> empty
    _ -> keyword annotationsC <+> 
          vcat (punctuate comma (map ( \(Annotation ans ap av) -> printAnnotations ans $+$ pretty (Annotation [] ap av)) l) )

instance Pretty a => Pretty (AnnotatedList a) where
    pretty = printAnnotatedList

printAnnotatedList :: Pretty a => AnnotatedList a -> Doc
printAnnotatedList (AnnotatedList l) =
  vcat $ punctuate comma $ map
    ( \ (ans, a) -> printAnnotations ans $+$ pretty a) l

instance Pretty FrameBit where
    pretty = printFrameBit

printFrameBit :: FrameBit -> Doc
printFrameBit fb = case fb of
    AnnotationFrameBit x -> printAnnotations x
    AnnotationBit ed l -> printRelation ed <+> pretty l
    AnnotationDR dr l -> printDomainOrRange dr <+> pretty l
    DatatypeBit ans a -> printAnnotations ans $+$ keyword equivalentToC <+> pretty a
    ExpressionBit x y -> printRelation x <+> pretty y
    ClassDisjointUnion a x -> keyword disjointUnionOfC
      <+> (printAnnotations a $+$ vcat(punctuate comma ( map (\p -> pretty p) x )))
    ClassHasKey a op dp -> keyword hasKeyC <+> (printAnnotations a
      $+$ vcat (punctuate comma $ map pretty op ++ map pretty dp))
    ObjectBit dr x -> printRelation dr <+> pretty x
    ObjectDomainOrRange dr x -> printDomainOrRange dr <+> pretty x
    ObjectCharacteristics x -> keyword characteristicsC <+> pretty x
    ObjectSubPropertyChain a opl -> keyword subPropertyChainC
      <+> (printAnnotations a $+$ fsep (prepPunctuate (keyword oS <> space) $ map pretty opl))
    DataBit dr x -> printRelation dr <+> pretty x
    DataPropRange x -> keyword rangeC <+> pretty x
    DataPropDomain x -> keyword domainC <+> pretty x
    DataFunctional x -> keyword characteristicsC <+> (printAnnotations x $+$ printCharact functionalS)
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

printFrame :: Frame -> Doc
printFrame f = case f of
    Frame (Entity e uri) bl -> pretty (showEntityType e) <+> fsep [pretty uri, vcat (map pretty bl)]
    MiscFrame e a misc -> case misc of
        MiscEquivOrDisjointClasses c -> printEquivOrDisjointClasses e <+> (printAnnotations a $+$ vcat (punctuate comma (map pretty c) ))
        MiscEquivOrDisjointObjProp c -> printEquivOrDisjointObj e <+> (printAnnotations a $+$ vcat ( punctuate comma (map pretty c) ))
        MiscEquivOrDisjointDataProp c -> printEquivOrDisjointData e <+> (printAnnotations a $+$ vcat ( punctuate comma (map pretty c) ))
    MiscSameOrDifferent s a c -> printSameOrDifferentInd s <+> (printAnnotations a $+$ vcat( punctuate comma (map pretty c) ))

printEquivOrDisjointClasses :: Relation -> Doc
printEquivOrDisjointClasses x = case x of
    Equivalent -> text "EquivalentClasses:"
    Disjoint -> text "DisjointClasses:"
    _ -> empty

printEquivOrDisjointObj :: Relation -> Doc
printEquivOrDisjointObj x = case x of
    Equivalent -> text "EquivalentProperties:"
    Disjoint -> text "DisjointProperties:"
    _ -> empty

printEquivOrDisjointData :: Relation -> Doc
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

printPrefixes :: PrefixMap -> Doc
printPrefixes x = vcat (map (\(a, b) ->
       (text "Prefix:" <+> text a <> colon <+> text ('<' : b ++ ">"))) (Map.toList x))

printOntology :: MOntology -> Doc
printOntology MOntology {muri = a, imports = b, ann = c, ontologyFrame = d} = keyword ontologyC
      <+> pretty a $++$ vcat (map printImport b) $++$ vcat (map printAnnotations c) $+$ vcat(map pretty d)

printOntologyDocument :: OntologyDocument -> Doc
printOntologyDocument OntologyDocument {prefixDeclaration = a, mOntology = b} = printPrefixes a $++$ pretty b

instance Pretty OntologyDocument where
    pretty = printOntologyDocument
