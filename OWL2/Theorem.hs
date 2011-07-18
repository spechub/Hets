module OWL2.Theorem where

import OWL2.AS
import OWL2.MS
import Data.List

-- | Adding annotations for theorems
addImplied :: Axiom -> Axiom
addImplied a = case remImplied a of
      PlainAxiom eith fb -> case eith of
        Misc ans -> PlainAxiom (Misc (impliedTh: ans)) fb
        _ -> case fb of
              ListFrameBit mr lfb -> PlainAxiom eith
                      $ ListFrameBit mr (addImplListFB lfb)
              AnnFrameBit ans afb -> PlainAxiom eith
                      $ AnnFrameBit (impliedTh : ans) afb

addImplListFB :: ListFrameBit -> ListFrameBit
addImplListFB lfb = case lfb of
    AnnotationBit a -> AnnotationBit $ addImpliedAnnList a
    ExpressionBit a -> ExpressionBit $ addImpliedAnnList a
    ObjectBit a -> ObjectBit $ addImpliedAnnList a
    DataBit a -> DataBit $ addImpliedAnnList a
    IndividualSameOrDifferent a -> IndividualSameOrDifferent
                        $ addImpliedAnnList a
    ObjectCharacteristics a -> ObjectCharacteristics
                        $ addImpliedAnnList a
    DataPropRange a -> DataPropRange $ addImpliedAnnList a
    IndividualFacts a -> IndividualFacts $ addImpliedAnnList a

addImpliedAnnList :: AnnotatedList a -> AnnotatedList a
addImpliedAnnList [] = []
addImpliedAnnList ((ans, b) : t) = (impliedTh : ans, b) : t

remImplied :: Axiom -> Axiom
remImplied (PlainAxiom eith fb) = case eith of
      Misc ans -> PlainAxiom (Misc (remImpliedList ans)) fb
      _ -> PlainAxiom eith
         (
          case fb of
            ListFrameBit mr lfb -> ListFrameBit mr (remImplListFB lfb)
            AnnFrameBit ans afb -> AnnFrameBit (remImpliedList ans) afb
         )

remImplListFB :: ListFrameBit -> ListFrameBit
remImplListFB lfb = case lfb of
    AnnotationBit a -> AnnotationBit $ remImpliedAnnList a
    ExpressionBit a -> ExpressionBit $ remImpliedAnnList a
    ObjectBit a -> ObjectBit $ remImpliedAnnList a
    DataBit a -> DataBit $ remImpliedAnnList a
    IndividualSameOrDifferent a -> IndividualSameOrDifferent
                        $ remImpliedAnnList a
    ObjectCharacteristics a -> ObjectCharacteristics
                        $ remImpliedAnnList a
    DataPropRange a -> DataPropRange $ remImpliedAnnList a
    IndividualFacts a -> IndividualFacts $ remImpliedAnnList a

remImplied1 :: (Annotations, a) -> (Annotations, a)
remImplied1 (ans, b) = (remImpliedList ans, b)

remImpliedList :: Annotations -> Annotations
remImpliedList = filter (not . isToProve1)

remImpliedAnnList :: AnnotatedList a -> AnnotatedList a
remImpliedAnnList = map remImplied1

impliedTh :: Annotation
impliedTh = Annotation [] (mkQName "Implied")
  . AnnValLit . Literal "true" . Typed $ mkQName "string"

isToProve1 :: Annotation -> Bool
isToProve1 anno = case anno of
      Annotation _ aIRI (AnnValLit (Literal value (Typed _))) ->
          localPart aIRI == "Implied" && isInfixOf "true" value
      _ -> False

isToProveList :: (Annotations, a) -> Bool
isToProveList (ans, _) = any isToProve1 ans

isToProveAnnList :: AnnotatedList a -> Bool
isToProveAnnList = any isToProveList

isToProve :: Axiom -> Bool
isToProve (PlainAxiom eith fb) = case eith of
      Misc ans -> any isToProve1 ans
      _ -> case fb of
        ListFrameBit _ lfb -> isToProveLB lfb
        AnnFrameBit ans _ -> any isToProve1 ans

isToProveLB :: ListFrameBit -> Bool
isToProveLB fb = case fb of
    AnnotationBit a -> isToProveAnnList a
    ExpressionBit a -> isToProveAnnList a
    ObjectBit a -> isToProveAnnList a
    DataBit a -> isToProveAnnList a
    IndividualSameOrDifferent a -> isToProveAnnList a
    ObjectCharacteristics a -> isToProveAnnList a
    DataPropRange a -> isToProveAnnList a
    IndividualFacts a -> isToProveAnnList a
