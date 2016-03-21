{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, University of Madgeburg, 2016
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till@iws.cs.ovgu.de
Stability   :  provisional
Portability :  portable

Pretty printing for the functional-style syntax of OWL 2
-}

module OWL2.FunctionalPrint where

import Common.Doc
import Common.DocUtils
import Common.AS_Annotation as Anno
import Common.Lib.State

import OWL2.AS
import OWL2.Extract
import OWL2.MS
import OWL2.Sign
import OWL2.Theorem
import OWL2.FunctionalPrintBasic
import OWL2.Keywords
import OWL2.ColonKeywords

import Data.Function
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set

-- | OWL2 signature printing

printOneNamed :: Anno.Named Axiom -> Doc
printOneNamed ns = printAxiom
  $ (if Anno.isAxiom ns then rmImplied else addImplied) $ Anno.sentence ns

delTopic :: Extended -> Sign -> Sign
delTopic e s = case e of
  ClassEntity (Expression c) -> s { concepts = Set.delete c $ concepts s }
  ObjectEntity (ObjectProp o) -> s
    { objectProperties = Set.delete o $ objectProperties s }
  SimpleEntity et -> execState (modEntity Set.delete et) s
  _ -> s

groupAxioms :: [Axiom] -> [Frame]
groupAxioms =
  concatMap (\ l@(PlainAxiom e _ : _) -> case e of
    Misc _ -> map (Frame e . (: []) . axiomBit) l
    _ -> [Frame e $ map axiomBit l])
  . groupBy (on (==) axiomTopic) . sortBy (on compare axiomTopic)

printOWLBasicTheory :: (Sign, [Named Axiom]) -> Doc
printOWLBasicTheory = printBasicTheory . prepareBasicTheory

prepareBasicTheory :: (Sign, [Named Axiom]) -> (Sign, [Named Axiom])
prepareBasicTheory (s, l) =
  (s { prefixMap = Map.union (prefixMap s) predefPrefixes }, l)

printBasicTheory :: (Sign, [Named Axiom]) -> Doc
printBasicTheory = printOntologyDocument . convertBasicTheory

convertBasicTheory :: (Sign, [Named Axiom]) -> OntologyDocument
convertBasicTheory (sig, l) = let
  (axs, ths) = partition Anno.isAxiom l
  cnvrt f = map f . groupAxioms . map Anno.sentence
  s = foldr (delTopic . axiomTopic . sentence) sig l
  in OntologyDocument (prefixMap s) $ emptyOntology
  $ toDecl s ++ cnvrt rmImpliedFrame axs ++ cnvrt addImpliedFrame ths

printSignElem :: Pretty a => Sign -> String -> (Sign -> Set.Set a) -> Doc
printSignElem s ty f = vcat $ map (\ t -> keyword ty <+> pretty t)
    $ Set.toList $ f s

printSign :: Sign -> Doc
printSign s = vcat
    (map (\ (c, l) -> hsep $ map text [prefixC, c ++ ":", '<' : l ++ ">"])
    $ Map.toList $ prefixMap s)
        $++$ foldl1 ($++$) (map (uncurry $ printSignElem s)
                [ ("Declaration(Datatype(", datatypes)
                , ("Declaration(Class(", concepts)
                , ("Declaration(ObjectProperty(", objectProperties)
                , ("Declaration(DataProperty(", dataProperties)
                , ("Declaration(NamedIndividual(", individuals)
                , ("Declaration(AnnotationProperty(", annotationRoles) ])



printFact :: Fact -> Doc
printFact pf = case pf of
    ObjectPropertyFact pn op i -> printPositiveOrNegative pn
           <+> pretty op <+> pretty i
    DataPropertyFact pn dp l -> printPositiveOrNegative pn
           <+> pretty dp <+> pretty l



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
printMisc a f r anl = f r <+> parens (printAnnotations a $+$ printAnnotatedList anl) 

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

printFrameBit :: Pretty a => a -> FrameBit -> Doc
printFrameBit ce fb = case fb of
    ListFrameBit r lfb -> case r of
        Just rel -> printRelation rel <> parens (pretty ce <+> printListFrameBit lfb)
        Nothing -> case lfb of
            ObjectCharacteristics x -> 
                vcat $ map (\(_,y) -> pretty y <> parens (pretty ce)) x -- annos!
            DataPropRange x -> keyword rangeC <+> printAnnotatedList x
            IndividualFacts x -> keyword factsC <+> (vcat $  map
                                  ( \ (ans, a) -> printAnnotations ans $+$ printFact a) x)
            _ -> empty
    AnnFrameBit a afb -> printAnnFrameBit a afb

showEntityTypeF :: EntityType -> String
showEntityTypeF e = case e of
    Datatype -> "Declaration(DataType("
    Class -> "Declaration(Class("
    ObjectProperty -> "Declaration(ObjectProperty("
    DataProperty -> "Declaration(DataProperty("
    AnnotationProperty -> "Declaration(AnnotationProperty("
    NamedIndividual -> "Declaration(NamedIndividual("

printFrame :: Frame -> Doc
printFrame (Frame eith bl) = case eith of
    SimpleEntity (Entity _ e uri) -> 
            text (showEntityTypeF e) <> pretty uri <> text "))"
            $+$ fsep [vcat (map (printFrameBit uri) bl)] 
    ObjectEntity ope -> 
            text "Declaration(ObjectProperty(" <> pretty ope <> text "))"
              $+$ fsep [vcat (map (printFrameBit ope) bl)] 
    ClassEntity ce -> 
            (if isBasicClass ce then 
              text "Declaration(Class(" <> pretty ce <> text "))"
              else empty)
            $+$ fsep [vcat (map (printFrameBit ce) bl)]
    Misc a -> case bl of
        [ListFrameBit (Just r) lfb] -> printMiscBit r a lfb
        [AnnFrameBit ans (AnnotationFrameBit Assertion)] ->
            let [Annotation _ iri _] = a
            in keyword individualC <+> (pretty iri $+$ printAnnotations ans)
        h : r -> printFrame (Frame eith [h])
          $+$ printFrame (Frame eith r)
        [] -> empty

printAxiom :: Axiom -> Doc
printAxiom (PlainAxiom e fb) = printFrame (Frame e [fb])

printImport :: ImportIRI -> Doc
printImport x = keyword importC <+> pretty x

printPrefixes :: PrefixMap -> Doc
printPrefixes x = vcat (map (\ (a, b) ->
       (text "Prefix(" <+> text a <> text ":=" <+> text ('<' : b ++ ">)")))
          (Map.toList x))

printOntology :: Ontology -> Doc
printOntology Ontology {name = a, imports = b, ann = c, ontFrames = d} =
    (if nullQName == a then empty else keyword ontologyC <+> pretty a)
    $++$ vcat (map printImport b)
    $++$ vcat (map printAnnotations c) $+$ vcat (map printFrame d)

printOntologyDocument :: OntologyDocument -> Doc
printOntologyDocument OntologyDocument {prefixDeclaration = a, ontology = b} =
    printPrefixes a $++$ printOntology b

