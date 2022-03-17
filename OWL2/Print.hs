{- |
Module      :  ./OWL2/Print.hs
Copyright   :  (c) Heng Jiang, Uni Bremen 2005-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Pretty printing for the Manchester Syntax of OWL 2.
-}

module OWL2.Print where

import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Keywords
import Common.IRI

import qualified OWL2.AS as AS
import OWL2.MS
import OWL2.Symbols
import OWL2.Keywords
import OWL2.ColonKeywords

import Data.List

instance Pretty AS.Character where
    pretty = printCharact . show

printCharact :: String -> Doc
printCharact = text

printIRI :: IRI -> Doc
printIRI q
    | ((hasFullIRI q || prefixName q `elem` ["", "owl", "rdfs"])
       && AS.isPredefPropOrClass q)
       || AS.isDatatypeKey q = keyword $ AS.getPredefName q
    | otherwise = text $ showIRI q

printDataIRI :: IRI -> Doc
printDataIRI q = if AS.isDatatypeKey q then text $ showIRI $ AS.setDatatypePrefix q
 else printIRI q

-- | Symbols printing

instance Pretty ExtEntityType where
    pretty ety = case ety of
        AnyEntity -> empty
        EntityType ty -> keyword $ show ty
        PrefixO -> keyword "Prefix"

instance Pretty SymbItems where
    pretty (SymbItems m us) = pretty m
        <+> ppWithCommas us

instance Pretty SymbMapItems where
    pretty (SymbMapItems m us) = pretty m
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
        APrefix p -> pretty p

cardinalityType :: AS.CardinalityType -> Doc
cardinalityType = keyword . AS.showCardinalityType

quantifierType :: AS.QuantifierType -> Doc
quantifierType = keyword . AS.showQuantifierType

printRelation :: AS.Relation -> Doc
printRelation = keyword . AS.showRelation

printEquivOrDisjointClasses :: AS.EquivOrDisjoint -> Doc
printEquivOrDisjointClasses x = case x of
    AS.Equivalent -> text "EquivalentClasses:"
    AS.Disjoint -> text "DisjointClasses:"

printEquivOrDisjointProp :: AS.EquivOrDisjoint -> Doc
printEquivOrDisjointProp e = case e of
    AS.Disjoint -> text "DisjointProperties:"
    AS.Equivalent -> text "EquivalentProperties:"

printPositiveOrNegative :: AS.PositiveOrNegative -> Doc
printPositiveOrNegative x = case x of
    AS.Positive -> empty
    AS.Negative -> keyword notS

printSameOrDifferentInd :: AS.SameOrDifferent -> Doc
printSameOrDifferentInd x = case x of
    AS.Same -> keyword sameIndividualC
    AS.Different -> keyword differentIndividualsC

instance Pretty AS.Entity where
    pretty (AS.Entity _ ty e) = keyword (show ty) <+> pretty e

instance Pretty AS.Literal where
    pretty lit = case lit of
        AS.Literal lexi ty -> let
          escapeDQ c s = case s of
            "" -> ""
            h : t -> case h of
              '\\' -> h : escapeDQ (c + 1 :: Int) t
              _ | odd c || h /= '"' -> h : escapeDQ 0 t
              _ -> '\\' : h : escapeDQ 0 t
          in plainText ('"' : escapeDQ 0 lexi ++ "\"") <> case ty of
            AS.Typed u -> keyword AS.cTypeS <> printDataIRI u
            AS.Untyped tag -> case tag of
              Nothing -> empty
              Just tag2 -> text asP <> text tag2
        AS.NumberLit f -> text (show f)

instance Pretty AS.ObjectPropertyExpression where
    pretty = printObjPropExp

printObjPropExp :: AS.ObjectPropertyExpression -> Doc
printObjPropExp obExp = case obExp of
    AS.ObjectProp ou -> pretty ou
    AS.ObjectInverseOf iopExp -> keyword inverseS <+> printObjPropExp iopExp

printFV :: (AS.ConstrainingFacet, AS.RestrictionValue) -> Doc
printFV (facet, restValue) = pretty (fromCF facet) <+> pretty restValue

fromCF :: AS.ConstrainingFacet -> String
fromCF f
    | hasFullIRI f = showIRICompact f \\ "http://www.w3.org/2001/XMLSchema#"
    | otherwise = show $ iriPath f

instance Pretty DatatypeFacet where
    pretty = keyword . showFacet

-- | Printing the DataRange
instance Pretty AS.DataRange where
    pretty = printDataRange

printDataRange :: AS.DataRange -> Doc
printDataRange dr = case dr of
    AS.DataType dtype l -> pretty dtype <+>
      if null l then empty else brackets $ sepByCommas $ map printFV l
    AS.DataComplementOf drange -> keyword notS <+> pretty drange
    AS.DataOneOf constList -> specBraces $ ppWithCommas constList
    AS.DataJunction ty drlist -> let
      k = case ty of
          AS.UnionOf -> orS
          AS.IntersectionOf -> andS
      in fsep $ prepPunctuate (keyword k <> space) $ map pretty drlist

-- | Printing the ClassExpression
instance Pretty AS.ClassExpression where
  pretty desc = case desc of
   AS.Expression ocUri -> printIRI ocUri
   AS.ObjectJunction ty ds -> let
      (k, p) = case ty of
          AS.UnionOf -> (orS, pretty)
          AS.IntersectionOf -> (andS, printPrimary)
      in fsep $ prepPunctuate (keyword k <> space) $ map p ds
   AS.ObjectComplementOf d -> keyword notS <+> printNegatedPrimary d
   AS.ObjectOneOf indUriList -> specBraces $ ppWithCommas indUriList
   AS.ObjectValuesFrom ty opExp d ->
      printObjPropExp opExp <+> quantifierType ty <+> printNegatedPrimary d
   AS.ObjectHasSelf opExp ->
      printObjPropExp opExp <+> keyword selfS
   AS.ObjectHasValue opExp indUri ->
      pretty opExp <+> keyword valueS <+> pretty indUri
   AS.ObjectCardinality (AS.Cardinality ty card opExp maybeDesc) ->
      printObjPropExp opExp <+> cardinalityType ty
        <+> text (show card)
        <+> maybe (keyword "Thing") printPrimary maybeDesc
   AS.DataValuesFrom ty dpExp dRange ->
       printIRI (head dpExp) <+> quantifierType ty
        <+> pretty dRange
   AS.DataHasValue dpExp cons -> pretty dpExp <+> keyword valueS <+> pretty cons
   AS.DataCardinality (AS.Cardinality ty card dpExp maybeRange) ->
       pretty dpExp <+> cardinalityType ty <+> text (show card)
         <+> maybe empty pretty maybeRange

printPrimary :: AS.ClassExpression -> Doc
printPrimary d = let dd = pretty d in case d of
  AS.ObjectJunction {} -> parens dd
  _ -> dd

printNegatedPrimary :: AS.ClassExpression -> Doc
printNegatedPrimary d = let r = parens $ pretty d in case d of
  AS.ObjectComplementOf _ -> r
  AS.ObjectValuesFrom {} -> r
  AS.DataValuesFrom {} -> r
  AS.ObjectHasValue {} -> r
  AS.DataHasValue {} -> r
  _ -> printPrimary d

-- | annotations printing
instance Pretty AS.AnnotationValue where
    pretty x = case x of
        AS.AnnAnInd i -> pretty i
        AS.AnnValue iri -> pretty iri
        AS.AnnValLit lit -> pretty lit

instance Pretty AS.Annotation where
    pretty = printAnnotation

printAnnotation :: AS.Annotation -> Doc
printAnnotation (AS.Annotation ans ap av) =
    sep [printAnnotations ans, sep [pretty ap, pretty av]]

printAnnotations :: Annotations -> Doc
printAnnotations l = case l of
    [] -> empty
    _ -> keyword annotationsC <+>
          vcat (punctuate comma (map (\ (AS.Annotation ans ap av) ->
            printAnnotations ans $+$ pretty (AS.Annotation [] ap av)) l) )

printAnnotatedList :: Pretty a => AnnotatedList a -> Doc
printAnnotatedList l =
    vcat $ punctuate comma $ map
        ( \ (ans, a) -> printAnnotations ans $+$ pretty a) l
