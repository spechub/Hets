{- |
Module      :  ./OWL2/Theorem.hs
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Adds the "implied" annotation - for specifying theorems
-}

module OWL2.Theorem where

import Common.IRI
import OWL2.AS
import OWL2.MS

import Data.List

implied :: Annotation
implied = Annotation [] (mkIRI "Implied")
  . AnnValLit . Literal "true" . Typed $ mkIRI "string"

rmList :: Annotations -> Annotations
rmList = filter (not . prove1)

rmAnnList :: AnnotatedList a -> AnnotatedList a
rmAnnList = map (\ (ans, b) -> (rmList ans, b) )

rmLFB :: ListFrameBit -> ListFrameBit
rmLFB lfb = case lfb of
    AnnotationBit a -> AnnotationBit $ rmAnnList a
    ExpressionBit a -> ExpressionBit $ rmAnnList a
    ObjectBit a -> ObjectBit $ rmAnnList a
    DataBit a -> DataBit $ rmAnnList a
    IndividualSameOrDifferent a -> IndividualSameOrDifferent $ rmAnnList a
    ObjectCharacteristics a -> ObjectCharacteristics $ rmAnnList a
    DataPropRange a -> DataPropRange $ rmAnnList a
    IndividualFacts a -> IndividualFacts $ rmAnnList a

rmFB :: FrameBit -> FrameBit
rmFB fb = case fb of
    ListFrameBit mr lfb -> ListFrameBit mr (rmLFB lfb)
    AnnFrameBit ans afb -> AnnFrameBit (rmList ans) afb

rmImplied :: Axiom -> Axiom
rmImplied (PlainAxiom eith fb) = case eith of
      Misc ans -> PlainAxiom (Misc $ rmList ans) $ rmFB fb
      _ -> PlainAxiom eith $ rmFB fb

rmImpliedFrame :: Frame -> Frame
rmImpliedFrame (Frame eith l) = case eith of
      Misc ans -> Frame (Misc $ rmList ans) $ map rmFB l
      _ -> Frame eith $ map rmFB l

addAnnList :: AnnotatedList a -> AnnotatedList a
addAnnList [] = []
addAnnList ((ans, b) : t) = (implied : ans, b) : t

addListFB :: ListFrameBit -> ListFrameBit
addListFB lfb = case lfb of
    AnnotationBit a -> AnnotationBit $ addAnnList a
    ExpressionBit a -> ExpressionBit $ addAnnList a
    ObjectBit a -> ObjectBit $ addAnnList a
    DataBit a -> DataBit $ addAnnList a
    IndividualSameOrDifferent a -> IndividualSameOrDifferent $ addAnnList a
    ObjectCharacteristics a -> ObjectCharacteristics $ addAnnList a
    DataPropRange a -> DataPropRange $ addAnnList a
    IndividualFacts a -> IndividualFacts $ addAnnList a

addImpliedFrameBit :: FrameBit -> FrameBit
addImpliedFrameBit fb = case fb of
    ListFrameBit mr lfb -> ListFrameBit mr (addListFB lfb)
    AnnFrameBit ans afb -> AnnFrameBit (implied : ans) afb

addImplied :: Axiom -> Axiom
addImplied a = case rmImplied a of
      PlainAxiom eith fb -> case eith of
        Misc ans -> PlainAxiom (Misc $ implied : ans) fb
        _ -> PlainAxiom eith $ addImpliedFrameBit fb

addImpliedFrame :: Frame -> Frame
addImpliedFrame a = case rmImpliedFrame a of
      Frame eith l -> case eith of
        Misc ans -> Frame (Misc $ implied : ans) l
        _ -> Frame eith $ map addImpliedFrameBit l

prove1 :: Annotation -> Bool
prove1 anno = case anno of
      Annotation _ aIRI (AnnValLit (Literal value (Typed _))) ->
          show (iriPath aIRI) == "Implied" && isInfixOf "true" value
      _ -> False

proveList :: (Annotations, a) -> Bool
proveList (ans, _) = any prove1 ans

proveAnnList :: AnnotatedList a -> Bool
proveAnnList = any proveList

proveLFB :: ListFrameBit -> Bool
proveLFB fb = case fb of
    AnnotationBit a -> proveAnnList a
    ExpressionBit a -> proveAnnList a
    ObjectBit a -> proveAnnList a
    DataBit a -> proveAnnList a
    IndividualSameOrDifferent a -> proveAnnList a
    ObjectCharacteristics a -> proveAnnList a
    DataPropRange a -> proveAnnList a
    IndividualFacts a -> proveAnnList a

proveFB :: FrameBit -> Bool
proveFB fb = case fb of
    ListFrameBit _ lfb -> proveLFB lfb
    AnnFrameBit ans _ -> any prove1 ans

prove :: Axiom -> Bool
prove (PlainAxiom eith fb) = case eith of
      Misc ans -> any prove1 ans || proveFB fb
      _ -> proveFB fb
