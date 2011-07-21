{- |
Module      :  $Header$
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisionalM
Portability :  portable

Expansion of all IRIs in the Ontology
-}

module OWL2.Expand (expF, expODoc) where

import OWL2.AS
import OWL2.MS

import Data.Maybe
import qualified Data.Map as Map

{- expanding all IRIs according to the prefix map from the sign
 the result is stored in the expandedIRI field of data QName -}

expand :: PrefixMap -> IRI -> IRI
expand pm qn =
  let np = namePrefix qn
      lp = localPart qn
  in if isFullIri qn then qn {expandedIRI = np ++ ":" ++ lp}
      else
        let expn = fromMaybe (error $ np ++ ": prefix not found ")
              $ Map.lookup np pm
        in qn {expandedIRI = expn ++ lp}

expDataRange :: PrefixMap -> DataRange -> DataRange
expDataRange s dra = case dra of
  DataType dt ls -> DataType (expand s dt)
     $ map (\ (cf, rv) -> (expand s cf, rv)) ls
  DataJunction jt drl -> DataJunction jt $ map (expDataRange s) drl
  DataComplementOf dr -> DataComplementOf $ expDataRange s dr
  _ -> dra

expOP :: PrefixMap -> ObjectPropertyExpression -> ObjectPropertyExpression
expOP s opr = case opr of
  ObjectProp op -> ObjectProp $ expand s op
  ObjectInverseOf op -> ObjectInverseOf $ expOP s op

expCE :: PrefixMap -> ClassExpression -> ClassExpression
expCE s cle = case cle of
  Expression c -> Expression $ expand s c
  ObjectJunction jt cel -> ObjectJunction jt $ map (expCE s) cel
  ObjectComplementOf ce -> ObjectComplementOf $ expCE s ce
  ObjectOneOf il -> ObjectOneOf $ map (expand s) il
  ObjectValuesFrom qt op ce ->
      ObjectValuesFrom qt (expOP s op) (expCE s ce)
  ObjectHasValue op i -> ObjectHasValue (expOP s op) (expand s i)
  ObjectHasSelf op -> ObjectHasSelf (expOP s op)
  ObjectCardinality (Cardinality ct i op mce) ->
      case mce of
        Nothing -> ObjectCardinality
              (Cardinality ct i (expOP s op) Nothing)
        Just ce -> ObjectCardinality
              (Cardinality ct i (expOP s op) $ Just (expCE s ce))
  DataValuesFrom qt dp dr -> DataValuesFrom qt
              (expand s dp) (expDataRange s dr)
  DataHasValue dp l -> DataHasValue (expand s dp) l
  DataCardinality (Cardinality ct i dp mdr) ->
      case mdr of
        Nothing -> DataCardinality
              (Cardinality ct i (expand s dp) Nothing)
        Just dr -> DataCardinality
              (Cardinality ct i (expand s dp) $ Just (expDataRange s dr))

expAnn :: PrefixMap -> Annotation -> Annotation
expAnn s (Annotation al ap av) = Annotation (map (expAnn s) al)
          (expand s ap) (expAV s av)

expAV :: PrefixMap -> AnnotationValue -> AnnotationValue
expAV s av = case av of
  AnnValue iri -> AnnValue $ expand s iri
  _ -> av

expAL :: PrefixMap -> (PrefixMap -> a -> a) ->
        AnnotatedList a -> AnnotatedList a
expAL s f = map (\ (ans, a) -> (map (expAnn s) ans, f s a))

expFact :: PrefixMap -> Fact -> Fact
expFact s f = case f of
  ObjectPropertyFact pn op i ->
        ObjectPropertyFact pn (expOP s op) (expand s i)
  DataPropertyFact pn dp l -> DataPropertyFact pn (expand s dp) l

expLFB :: PrefixMap -> ListFrameBit -> ListFrameBit
expLFB s lfb = case lfb of
  AnnotationBit al -> AnnotationBit $ expAL s expand al
  ExpressionBit al -> ExpressionBit $ expAL s expCE al
  ObjectBit al -> ObjectBit $ expAL s expOP al
  DataBit al -> DataBit $ expAL s expand al
  IndividualSameOrDifferent al ->
        IndividualSameOrDifferent $ expAL s expand al
  DataPropRange al -> DataPropRange $ expAL s expDataRange al
  IndividualFacts al -> IndividualFacts $ expAL s expFact al
  _ -> lfb

expAFB :: PrefixMap -> AnnFrameBit -> AnnFrameBit
expAFB s afb = case afb of
  DatatypeBit dr -> DatatypeBit $ expDataRange s dr
  ClassDisjointUnion cel -> ClassDisjointUnion $ map (expCE s) cel
  ClassHasKey opl dpl -> ClassHasKey (map (expOP s) opl)
        (map (expand s) dpl)
  ObjectSubPropertyChain opl -> ObjectSubPropertyChain (map (expOP s) opl)
  _ -> afb

expFB :: PrefixMap -> FrameBit -> FrameBit
expFB s fb = case fb of
  ListFrameBit mr lfb -> ListFrameBit mr $ expLFB s lfb
  AnnFrameBit ans afb -> AnnFrameBit (map (expAnn s) ans) $ expAFB s afb

expE :: PrefixMap -> Extended -> Extended
expE s ex = case ex of
  Misc ans -> Misc $ map (expAnn s) ans
  SimpleEntity (Entity ty e) -> SimpleEntity (Entity ty $ expand s e)
  ObjectEntity op -> ObjectEntity $ expOP s op
  ClassEntity ce -> ClassEntity $ expCE s ce

expF :: PrefixMap -> Frame -> Frame
expF s (Frame e fbl) = Frame (expE s e) $ map (expFB s) fbl

expA :: PrefixMap -> Axiom -> Axiom
expA s (PlainAxiom e fb) = PlainAxiom (expE s e) $ expFB s fb

expOnt :: PrefixMap -> Ontology -> Ontology
expOnt s o =
  let oiri = expand s $ name o
      imp = map (expand s) $ imports o
      ans = map (map (expAnn s)) $ ann o
      fr = map (expF s) $ ontFrames o
  in o {name = oiri, imports = imp, ann = ans, ontFrames = fr}

expODoc :: PrefixMap -> OntologyDocument -> OntologyDocument
expODoc s o = o {ontology = expOnt s $ ontology o}
