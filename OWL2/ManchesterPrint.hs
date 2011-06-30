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
import OWL2.Keywords
import OWL2.ColonKeywords
import qualified Data.Map as Map

printCharact :: String -> Doc
printCharact = text

instance Pretty Character where
  pretty = printCharact . show

instance Pretty a => Pretty (AnnotatedList a) where
    pretty = printAnnotatedList

printAnnotatedList :: Pretty a => AnnotatedList a -> Doc
printAnnotatedList (AnnotatedList l) =
  vcat $ punctuate comma $ map
    ( \ (ans, a) -> printAnnotations ans $+$ pretty a) l

instance Pretty FrameBit where
    pretty = printFrameBit

instance Pretty ListFrameBit where
    pretty = printListFrameBit

printListFrameBit :: ListFrameBit -> Doc
printListFrameBit lfb = case lfb of
    AnnotationBit a -> pretty a
    ExpressionBit a -> pretty a
    ObjectBit a -> pretty a
    DataBit a -> pretty a
    IndividualSameOrDifferent a -> pretty a 
    _ -> empty 

printFrameBit :: FrameBit -> Doc
printFrameBit fb = case fb of
  ListFrameBit r lfb -> case r of 
      Just rel -> printRelation rel <+> pretty lfb
      Nothing -> case lfb of
        ObjectCharacteristics x -> keyword characteristicsC <+> pretty x
        DataPropRange x -> keyword rangeC <+> pretty x
        IndividualFacts x -> keyword factsC <+> pretty x
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

printPositiveOrNegative :: PositiveOrNegative -> Doc
printPositiveOrNegative x = case x of
    Positive -> empty
    Negative -> keyword notS

instance Pretty Frame where
    pretty = printFrame

printFrame :: Frame -> Doc
printFrame f = case f of
    Frame eith bl -> case eith of
      Right (Entity e uri) -> pretty (showEntityType e) <+>
            fsep [pretty uri, vcat (map pretty bl)]
      Left a -> case bl of 
        [ListFrameBit (Just e) (ExpressionBit anl)] -> printEquivOrDisjointClasses (getED e) <+>
            (printAnnotations a $+$ pretty anl)
        [ListFrameBit (Just e) (ObjectBit anl)] -> printEquivOrDisjointProp (getED e) <+>
            (printAnnotations a $+$ pretty anl)
        [ListFrameBit (Just e) (DataBit anl)] -> printEquivOrDisjointProp (getED e) <+>
            (printAnnotations a $+$ pretty anl)
        [ListFrameBit (Just s) (IndividualSameOrDifferent anl)] -> printSameOrDifferentInd (getSD s) <+>
            (printAnnotations a $+$ pretty anl)
        _ -> empty

instance Pretty Axiom where
    pretty = printAxiom

printAxiom :: Axiom -> Doc
printAxiom (PlainAxiom e fb) = printFrame (Frame e [fb])

instance Pretty MOntology where
    pretty = printOntology

printImport :: ImportIRI -> Doc
printImport x = keyword importC <+> pretty x

printPrefixes :: PrefixMap -> Doc
printPrefixes x = vcat (map (\ (a, b) ->
       (text "Prefix:" <+> text a <> colon <+> text ('<' : b ++ ">")))
          (Map.toList x))

printOntology :: MOntology -> Doc
printOntology MOntology {muri = a, imports = b, ann = c, ontologyFrame = d} =
        keyword ontologyC <+> pretty a $++$ vcat (map printImport b)
        $++$ vcat (map printAnnotations c) $+$ vcat (map pretty d)

printOntologyDocument :: OntologyDocument -> Doc
printOntologyDocument OntologyDocument {prefixDeclaration = a, mOntology = b} =
        printPrefixes a $++$ pretty b

instance Pretty OntologyDocument where
    pretty = printOntologyDocument
