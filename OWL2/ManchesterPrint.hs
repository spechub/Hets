{- |
Module      :  $Header$
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Pretty printing for the Manchester Syntax of OWL 2
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
    printSign s { prefixMap = Map.union (prefixMap s) predefPrefixes }
    $++$ vsep (map (pretty . sentence) l)

instance Pretty Sign where
    pretty = printSign

printSignElem :: Pretty a => Sign -> String -> (Sign -> Set.Set a) -> Doc
printSignElem s ty f = vcat $ map (\ t -> keyword ty <+> pretty t)
    $ Set.toList $ f s

printSign :: Sign -> Doc
printSign s = vcat
    (map (\ (c, l) -> hsep $ map text [prefixC, c ++ ":", '<' : l ++ ">"])
    $ Map.toList $ prefixMap s)
        $++$ foldl1 ($++$) (map (uncurry $ printSignElem s)
                [ (datatypeC, datatypes)
                , (classC, concepts)
                , (objectPropertyC, objectProperties)
                , (dataPropertyC, dataProperties)
                , (individualC, individuals)
                , (annotationPropertyC, annotationRoles) ])

instance Pretty Fact where
    pretty = printFact

printFact :: Fact -> Doc
printFact pf = case pf of
    ObjectPropertyFact pn op i -> printPositiveOrNegative pn
           <+> pretty op <+> pretty i
    DataPropertyFact pn dp l -> printPositiveOrNegative pn
           <+> pretty dp <+> pretty l

instance Pretty ListFrameBit where
    pretty = printListFrameBit

-- | ListFrameBits only with relations
printListFrameBit :: ListFrameBit -> Doc
printListFrameBit lfb = case lfb of
    AnnotationBit a -> printAnnotatedList a
    ExpressionBit a -> printAnnotatedList a
    ObjectBit a -> printAnnotatedList a
    DataBit a -> printAnnotatedList a
    IndividualSameOrDifferent a -> printAnnotatedList a
    _ -> empty

printMisc :: Pretty a => Annotations -> (b -> Doc) -> b -> AnnotatedList a
    -> Doc
printMisc a f r anl = f r <+> (printAnnotations a $+$ printAnnotatedList anl)

-- | Misc ListFrameBits
printMiscBit :: Relation -> Annotations -> ListFrameBit -> Doc
printMiscBit r a lfb = case lfb of
    ExpressionBit anl -> printMisc a printEquivOrDisjointClasses (getED r) anl
    ObjectBit anl -> printMisc a printEquivOrDisjointProp (getED r) anl
    DataBit anl -> printMisc a printEquivOrDisjointProp (getED r) anl
    IndividualSameOrDifferent anl ->
        printMisc a printSameOrDifferentInd (getSD r) anl
    _ -> empty

printAnnFrameBit :: Annotations -> AnnFrameBit -> Doc
printAnnFrameBit a afb = case afb of
    AnnotationFrameBit _ -> printAnnotations a
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

instance Pretty FrameBit where
    pretty = printFrameBit

printFrameBit :: FrameBit -> Doc
printFrameBit fb = case fb of
    ListFrameBit r lfb -> case r of
        Just rel -> printRelation rel <+> pretty lfb
        Nothing -> case lfb of
            ObjectCharacteristics x -> keyword characteristicsC
                <+> printAnnotatedList x
            DataPropRange x -> keyword rangeC <+> printAnnotatedList x
            IndividualFacts x -> keyword factsC <+> printAnnotatedList x
            _ -> empty
    AnnFrameBit a afb -> printAnnFrameBit a afb

instance Pretty Frame where
    pretty = printFrame

printFrame :: Frame -> Doc
printFrame (Frame eith bl) = case eith of
    SimpleEntity (Entity e uri) -> keyword (showEntityType e) <+>
            fsep [pretty uri $+$ vcat (map pretty bl)]
    ObjectEntity ope -> keyword objectPropertyC <+>
            (pretty ope $+$ fsep [vcat (map pretty bl)])
    ClassEntity ce -> keyword classC <+>
            (pretty ce $+$ fsep [vcat (map pretty bl)])
    Misc a -> case bl of
        [ListFrameBit (Just r) lfb] -> printMiscBit r a lfb
        [AnnFrameBit ans (AnnotationFrameBit Assertion)] ->
            let [Annotation _ iri _] = a
            in keyword individualC <+> (pretty iri $+$ printAnnotations ans)
        _ -> empty

instance Pretty Axiom where
    pretty = printAxiom

printAxiom :: Axiom -> Doc
printAxiom (PlainAxiom e fb) = printFrame (Frame e [fb])

printImport :: ImportIRI -> Doc
printImport x = keyword importC <+> pretty x

printPrefixes :: PrefixMap -> Doc
printPrefixes x = vcat (map (\ (a, b) ->
       (text "Prefix:" <+> text a <> colon <+> text ('<' : b ++ ">")))
          (Map.toList x))

-- | Printing the ontology
instance Pretty Ontology where
    pretty = printOntology

printOntology :: Ontology -> Doc
printOntology Ontology {name = a, imports = b, ann = c, ontFrames = d} =
    (if nullQName == a then empty else keyword ontologyC <+> pretty a)
    $++$ vcat (map printImport b)
    $++$ vcat (map printAnnotations c) $+$ vcat (map pretty d)

printOntologyDocument :: OntologyDocument -> Doc
printOntologyDocument OntologyDocument {prefixDeclaration = a, ontology = b} =
    printPrefixes a $++$ pretty b

instance Pretty OntologyDocument where
    pretty = printOntologyDocument
