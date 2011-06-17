{- |
Module      :  $Header$
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Pretty printing for OWL 2 DL theories - Manchester Syntax.
-}

module OWL2.ManchesterPrint where

import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Keywords

import OWL2.AS
import OWL2.MS
import OWL2.Print
import OWL.Keywords
import OWL.ColonKeywords

import qualified Data.Set as Set
import qualified Data.Map as Map

instance Pretty Frame where
    pretty = printFrame

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
    _ -> keyword annotationsC <+> sepByCommas (map ( \(ans, a) -> pretty ans <+> pretty a) l )

instance Pretty a => Pretty (AnnotatedList a) where
    pretty = printAnnotatedList
    
printAnnotatedList :: Pretty a => AnnotatedList a -> Doc
printAnnotatedList (AnnotatedList l) = sepByCommas $ map ( \(ans, a) -> pretty ans <+> pretty a) l
  
printFrame :: Frame -> Doc
printFrame f = case f of
    ClassFrame c cfb -> classStart <+> pretty c $+$ pretty cfb

instance Pretty ClassFrameBit where
    pretty = printClassFrameBit

printClassFrameBit :: ClassFrameBit -> Doc
printClassFrameBit cfb = case cfb of
    ClassAnnotations x -> pretty x
    ClassSubClassOf x -> keyword subClassOfC <+> pretty x
    ClassEquivOrDisjoint x y -> printEquivOrDisjoint x <+> pretty y
    ClassDisjointUnion a x -> keyword disjointUnionOfC <+> pretty a <+> setToDocV (Set.fromList x)
    ClassHasKey a op dp -> keyword hasKeyC <+> pretty a
      <+> vcat (punctuate comma $ map pretty op ++ map pretty dp)

instance Pretty ObjectFrameBit where
    pretty = printObjectFrameBit

printObjectFrameBit :: ObjectFrameBit -> Doc
printObjectFrameBit ofb = case ofb of
    ObjectAnnotations x -> pretty x
    ObjectDomainOrRange dr x -> printObjDomainOrRange dr <+> pretty x
    ObjectCharacteristics x -> keyword characteristicsC <+> pretty x
    ObjectEquivOrDisjoint ed x -> printEquivOrDisjoint ed <+> pretty x
    ObjectInverse x -> keyword inverseOfC <+> printAnnotatedList x
    ObjectSubPropertyChain a opl -> keyword subPropertyChainC <+> pretty a <+> fsep (prepPunctuate (keyword oS <> space) $ map pretty opl)
    ObjectSubPropertyOf x -> keyword subPropertyOfC <+> pretty x

instance Pretty Character where
  pretty = printCharact . show 
{-
  = ObjectAnnotations Annotations
  | ObjectDomainOrRange ObjDomainOrRange (AnnotatedList ClassExpression)
  | ObjectCharacteristics (AnnotatedList Character)
  | ObjectEquivOrDisjoint EquivOrDisjoint (AnnotatedList ObjectPropertyExpression)
  | ObjectInverse (AnnotatedList ObjectPropertyExpression)
  | ObjectSubPropertyChain Annotations [ObjectPropertyExpression]
  | ObjectSubPropertyOf (AnnotatedList ObjectPropertyExpression)
-}
