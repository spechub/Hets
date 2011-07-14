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
import Common.AS_Annotation

import OWL2.AS
import OWL2.MS
import OWL2.Sign
import OWL2.Print
import OWL2.Keywords
import OWL2.ColonKeywords
import qualified Data.Map as Map
import qualified Data.Set as Set

-- | OWL2 signature printing

printOWLBasicTheory :: (Sign, [Named Axiom]) -> Doc
printOWLBasicTheory (s, l) =
  printSign s
  $++$ vsep (map (pretty . sentence) l)

instance Pretty Sign where
    pretty = printSign

printSign :: Sign -> Doc
printSign s =
   let cs = concepts s
       ts = datatypes s
   in vcat (map (\ (c, l) -> hsep $ map text
                 [prefixC, c ++ ":", '<' : l ++ ">"]
                )
      $ Map.toList $ Map.union (prefixMap s)
      $ Map.fromList [ ("owl", "http://www.w3.org/2002/07/owl#")
      , ("rdf", "http://www.w3.org/1999/02/22-rdf-syntax-ns#")
      , ("rdfs", "http://www.w3.org/2000/01/rdf-schema#")
      , ("xsd", "http://www.w3.org/2001/XMLSchema#")
      , ("", showQU dummyQName ++ "#") ] ) $++$
   vcat (map (\ t -> keyword datatypeC <+> pretty t) $ Set.toList ts)
   $++$ vcat (map (\ c -> keyword classC <+> pretty c) $ Set.toList cs)
   $++$ vcat (map (\ o -> keyword objectPropertyC <+> pretty o)
          $ Set.toList $ objectProperties s)
   $++$ vcat (map (\ d -> keyword dataPropertyC <+> pretty d)
          $ Set.toList $ dataProperties s)
   $++$ vcat (map (\ i -> keyword individualC <+> pretty i)
          $ Set.toList $ individuals s)
   $++$ vcat (map (\ i -> keyword annotationPropertyC <+> pretty i)
          $ Set.toList $ annotationRoles s)

-- | Printing the frame bits and the axioms
instance Pretty FrameBit where
    pretty = printFrameBit

instance Pretty ListFrameBit where
    pretty = printListFrameBit

printListFrameBit :: ListFrameBit -> Doc
printListFrameBit lfb = case lfb of
    AnnotationBit a -> printAnnotatedList a
    ExpressionBit a -> printAnnotatedList a
    ObjectBit a -> printAnnotatedList a
    DataBit a -> printAnnotatedList a
    IndividualSameOrDifferent a -> printAnnotatedList a 
    _ -> empty 

printFrameBit :: FrameBit -> Doc
printFrameBit fb = case fb of
  ListFrameBit r lfb -> case r of 
      Just rel -> printRelation rel <+> pretty lfb
      Nothing -> case lfb of
        ObjectCharacteristics x -> keyword characteristicsC <+> printAnnotatedList x
        DataPropRange x -> keyword rangeC <+> printAnnotatedList x
        IndividualFacts x -> keyword factsC <+> printAnnotatedList x
        _ -> empty
  AnnFrameBit a afb -> case afb of
    AnnotationFrameBit -> printAnnotations a
    DatatypeBit x -> printAnnotations a
          $+$ keyword equivalentToC <+> pretty x
    ClassDisjointUnion x -> keyword disjointUnionOfC
      <+> (printAnnotations a
          $+$ vcat (punctuate comma ( map pretty x )))
    ClassHasKey op dp -> keyword hasKeyC <+> (printAnnotations a
      $+$ vcat (punctuate comma $ map pretty op ++ map pretty dp))
    ObjectSubPropertyChain opl -> keyword subPropertyChainC
      <+> (printAnnotations a $+$ fsep (prepPunctuate (keyword oS <> space)
          $ map pretty opl))
    DataFunctional -> keyword characteristicsC <+>
          (printAnnotations a $+$ printCharact functionalS)

instance Pretty Fact where
    pretty = printFact

printFact :: Fact -> Doc
printFact pf = case pf of
    ObjectPropertyFact pn op i -> printPositiveOrNegative pn
           <+> pretty op <+> pretty i
    DataPropertyFact pn dp l -> printPositiveOrNegative pn
           <+> pretty dp <+> pretty l

instance Pretty Frame where
    pretty = printFrame

printFrame :: Frame -> Doc
printFrame (Frame eith bl) = case eith of
        SimpleEntity (Entity e uri) -> pretty (showEntityType e) <+>
            fsep [pretty uri $+$ vcat (map pretty bl)]
        ObjectEntity ope -> keyword objectPropertyC $+$ (pretty ope <+> fsep [vcat (map pretty bl)])
        ClassEntity ce -> keyword classC <+> (pretty ce $+$ fsep [vcat (map pretty bl)])
        Misc a -> case bl of 
          [ListFrameBit (Just e) (ExpressionBit anl)] -> printEquivOrDisjointClasses (getED e) <+>
            (printAnnotations a $+$ printAnnotatedList anl)
          [ListFrameBit (Just e) (ObjectBit anl)] -> printEquivOrDisjointProp (getED e) <+>
            (printAnnotations a $+$ printAnnotatedList anl)
          [ListFrameBit (Just e) (DataBit anl)] -> printEquivOrDisjointProp (getED e) <+>
            (printAnnotations a $+$ printAnnotatedList anl)
          [ListFrameBit (Just s) (IndividualSameOrDifferent anl)] -> printSameOrDifferentInd (getSD s) <+>
            (printAnnotations a $+$ printAnnotatedList anl)
          _ -> empty

instance Pretty Axiom where
    pretty = printAxiom

printAxiom :: Axiom -> Doc
printAxiom (PlainAxiom e fb) = printFrame (Frame e [fb])

-- | Printing the ontology
instance Pretty Ontology where
    pretty = printOntology

printImport :: ImportIRI -> Doc
printImport x = keyword importC <+> pretty x

printPrefixes :: PrefixMap -> Doc
printPrefixes x = vcat (map (\ (a, b) ->
       (text "Prefix:" <+> text a <> colon <+> text ('<' : b ++ ">")))
          (Map.toList x))

printOntology :: Ontology -> Doc
printOntology Ontology {name = a, imports = b, ann = c, ontFrames = d} =
        keyword ontologyC <+> pretty a $++$ vcat (map printImport b)
        $++$ vcat (map printAnnotations c) $+$ vcat (map pretty d)

printOntologyDocument :: OntologyDocument -> Doc
printOntologyDocument OntologyDocument {prefixDeclaration = a, ontology = b} =
        printPrefixes a $++$ pretty b

instance Pretty OntologyDocument where
    pretty = printOntologyDocument
