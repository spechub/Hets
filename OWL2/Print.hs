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

import OWL2.AS
import OWL2.MS
import OWL2.Symbols
import OWL2.Keywords
import OWL2.ColonKeywords

import Data.List

instance Pretty Character where
    pretty = printCharact . show

printCharact :: String -> Doc
printCharact = text

printIRI :: IRI -> Doc
printIRI q
    | ((hasFullIRI q || prefixName q `elem` ["", "owl", "rdfs"])
       && isPredefPropOrClass q)
       || isDatatypeKey q = keyword $ getPredefName q
    | otherwise = text $ showIRI q

printDataIRI :: IRI -> Doc
printDataIRI q = if isDatatypeKey q then text $ showIRI $ setDatatypePrefix q
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

cardinalityType :: CardinalityType -> Doc
cardinalityType = keyword . showCardinalityType

quantifierType :: QuantifierType -> Doc
quantifierType = keyword . showQuantifierType

printRelation :: Relation -> Doc
printRelation = keyword . showRelation

printEquivOrDisjointClasses :: EquivOrDisjoint -> Doc
printEquivOrDisjointClasses x = case x of
    Equivalent -> text "EquivalentClasses:"
    Disjoint -> text "DisjointClasses:"

printEquivOrDisjointProp :: EquivOrDisjoint -> Doc
printEquivOrDisjointProp e = case e of
    Disjoint -> text "DisjointProperties:"
    Equivalent -> text "EquivalentProperties:"

printPositiveOrNegative :: PositiveOrNegative -> Doc
printPositiveOrNegative x = case x of
    Positive -> empty
    Negative -> keyword notS

printSameOrDifferentInd :: SameOrDifferent -> Doc
printSameOrDifferentInd x = case x of
    Same -> keyword sameIndividualC
    Different -> keyword differentIndividualsC

instance Pretty Entity where
    pretty (Entity _ ty e) = keyword (show ty) <+> pretty e

instance Pretty Literal where
    pretty lit = case lit of
        Literal lexi ty -> let
          escapeDQ c s = case s of
            "" -> ""
            h : t -> case h of
              '\\' -> h : escapeDQ (c + 1 :: Int) t
              _ | odd c || h /= '"' -> h : escapeDQ 0 t
              _ -> '\\' : h : escapeDQ 0 t
          in plainText ('"' : escapeDQ 0 lexi ++ "\"") <> case ty of
            Typed u -> keyword cTypeS <> printDataIRI u
            Untyped tag -> case tag of
              Nothing -> empty
              Just tag2 -> text asP <> text tag2
        NumberLit f -> text (show f)

instance Pretty ObjectPropertyExpression where
    pretty = printObjPropExp

printObjPropExp :: ObjectPropertyExpression -> Doc
printObjPropExp obExp = case obExp of
    ObjectProp ou -> pretty ou
    ObjectInverseOf iopExp -> keyword inverseS <+> printObjPropExp iopExp

printFV :: (ConstrainingFacet, RestrictionValue) -> Doc
printFV (facet, restValue) = pretty (fromCF facet) <+> pretty restValue

fromCF :: ConstrainingFacet -> String
fromCF f
    | hasFullIRI f = showIRICompact f \\ "http://www.w3.org/2001/XMLSchema#"
    | otherwise = show $ iriPath f

instance Pretty DatatypeFacet where
    pretty = keyword . showFacet

-- | Printing the DataRange
instance Pretty DataRange where
    pretty = printDataRange

printDataRange :: DataRange -> Doc
printDataRange dr = case dr of
    DataType dtype l -> pretty dtype <+>
      if null l then empty else brackets $ sepByCommas $ map printFV l
    DataComplementOf drange -> keyword notS <+> pretty drange
    DataOneOf constList -> specBraces $ ppWithCommas constList
    DataJunction ty drlist -> let
      k = case ty of
          UnionOf -> orS
          IntersectionOf -> andS
      in fsep $ prepPunctuate (keyword k <> space) $ map pretty drlist

-- | Printing the ClassExpression
instance Pretty ClassExpression where
  pretty desc = case desc of
   Expression ocUri -> printIRI ocUri
   ObjectJunction ty ds -> let
      (k, p) = case ty of
          UnionOf -> (orS, pretty)
          IntersectionOf -> (andS, printPrimary)
      in fsep $ prepPunctuate (keyword k <> space) $ map p ds
   ObjectComplementOf d -> keyword notS <+> printNegatedPrimary d
   ObjectOneOf indUriList -> specBraces $ ppWithCommas indUriList
   ObjectValuesFrom ty opExp d ->
      printObjPropExp opExp <+> quantifierType ty <+> printNegatedPrimary d
   ObjectHasSelf opExp ->
      printObjPropExp opExp <+> keyword selfS
   ObjectHasValue opExp indUri ->
      pretty opExp <+> keyword valueS <+> pretty indUri
   ObjectCardinality (Cardinality ty card opExp maybeDesc) ->
      printObjPropExp opExp <+> cardinalityType ty
        <+> text (show card)
        <+> maybe (keyword "Thing") printPrimary maybeDesc
   DataValuesFrom ty dpExp dRange ->
       printIRI dpExp <+> quantifierType ty
        <+> pretty dRange
   DataHasValue dpExp cons -> pretty dpExp <+> keyword valueS <+> pretty cons
   DataCardinality (Cardinality ty card dpExp maybeRange) ->
       pretty dpExp <+> cardinalityType ty <+> text (show card)
         <+> maybe empty pretty maybeRange

printPrimary :: ClassExpression -> Doc
printPrimary d = let dd = pretty d in case d of
  ObjectJunction {} -> parens dd
  _ -> dd

printNegatedPrimary :: ClassExpression -> Doc
printNegatedPrimary d = let r = parens $ pretty d in case d of
  ObjectComplementOf _ -> r
  ObjectValuesFrom {} -> r
  DataValuesFrom {} -> r
  ObjectHasValue {} -> r
  DataHasValue {} -> r
  _ -> printPrimary d

-- | annotations printing
instance Pretty AnnotationValue where
    pretty x = case x of
        AnnValue iri -> pretty iri
        AnnValLit lit -> pretty lit

instance Pretty OWL2.AS.Annotation where
    pretty = printAnnotation

printAnnotation :: OWL2.AS.Annotation -> Doc
printAnnotation (Annotation ans ap av) =
    sep [printAnnotations ans, sep [pretty ap, pretty av]]

printAnnotations :: Annotations -> Doc
printAnnotations l = case l of
    [] -> empty
    _ -> keyword annotationsC <+>
          vcat (punctuate comma (map (\ (Annotation ans ap av) ->
            printAnnotations ans $+$ pretty (Annotation [] ap av)) l) )

printAnnotatedList :: Pretty a => AnnotatedList a -> Doc
printAnnotatedList l =
    vcat $ punctuate comma $ map
        ( \ (ans, a) -> printAnnotations ans $+$ pretty a) l

-- | printing Axioms

instance Pretty AxiomAnnotations where
    pretty = printAnnotations

instance Pretty ClassAxiom where
    pretty ca = case ca of 
        SubClassOf axAns subClExpr supClExpr -> printSubClassOf ca
        EquivalentClasses axAns clExprs -> printEquivalentClasses ca
        DisjointClasses axAns clExprs -> printDisjointClasses ca
        DisjointUnion axAns cl disjClExprs -> printDisjointUnion ca

printSubClassOf :: ClassAxiom -> Doc
printSubClassOf (SubClassOf axAns subClExpr supClExpr) =
    keyword "SubClassOf" <+>
    (parens . hsep $ (map pretty [axAns, subClExpr, supClExpr]))

printEquivalentClasses :: ClassAxiom -> Doc
printEquivalentClasses (EquivalentClasses axAns clExprs) =
    keyword "EquivalentClasses" <+>
    (parens . hsep . concat $ [[pretty axAns], map pretty clExprs])

printDisjointClasses :: ClassAxiom -> Doc
printDisjointClasses (DisjointClasses axAns clExprs) =
    keyword "DisjointClasses" <+>
    (parens . hsep . concat $ [[pretty axAns], map pretty clExprs])

printDisjointUnion :: ClassAxiom -> Doc
printDisjointUnion (DisjointUnion axAns cl disjClExprs) = 
    keyword "DisjointUnion" <+>
    (parens . hsep . concat $ [map pretty [axAns, cl],
        map pretty disjClExprs])

instance Pretty Axiom where
    pretty axiom = case axiom of
        ClassAxiom ca -> pretty ca
