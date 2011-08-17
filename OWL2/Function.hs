{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

{- |
Module      :  $Header$
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Instances for some of the functions used in OWL 2
    (currently, renaming and expanding IRIs)
-}

module OWL2.Function where

import OWL2.AS
import OWL2.MS
import OWL2.Sign

import qualified Data.Map as Map
import qualified Data.Set as Set

{- | this class contains general functions which operate on the ontology
    document, such as prefix renaming or IRI expansion -}
class Function a where
    function :: Action -> AMap -> a -> a

data Action = Rename | Expand
    deriving (Show, Eq, Ord)

type AMap = Map.Map String String

maybeDo :: (Function a) => Action -> AMap -> Maybe a -> Maybe a
maybeDo t mp = fmap $ function t mp

instance Function PrefixMap where
    function a mp oldPs = case a of
        Rename ->
            foldl (\ ns (pre, ouri) ->
                    Map.insert (Map.findWithDefault pre pre mp) ouri ns)
                Map.empty $ Map.toList oldPs
        Expand -> oldPs

instance Function IRI where
  function a pm qn = case a of
    Rename -> let pre = namePrefix qn in
        qn { namePrefix = Map.findWithDefault pre pre pm}
    Expand -> let np = namePrefix qn
                  lp = localPart qn
              in case iriType qn of
                Full -> qn {expandedIRI = np ++ ":" ++ lp}
                NodeID -> qn {expandedIRI = lp}
                _ -> let miri = Map.lookup np $ Map.union pm predefPrefixes
                     in case miri of
                        Just expn -> qn {expandedIRI = expn ++ lp}
                        Nothing -> error $ np ++ ": prefix not found"

instance Function Sign where
   function t mp (Sign p1 p2 p3 p4 p5 p6 p7) =
       Sign (Set.map (function t mp) p1)
            (Set.map (function t mp) p2)
            (Set.map (function t mp) p3)
            (Set.map (function t mp) p4)
            (Set.map (function t mp) p5)
            (Set.map (function t mp) p6)
            (function t mp p7)

instance Function Entity where
    function t pm (Entity ty ent) = Entity ty $ function t pm ent

instance Function Literal where
    function t pm l = case l of
        Literal lf (Typed dt) -> Literal lf $ Typed $ function t pm dt
        _ -> l

instance Function ObjectPropertyExpression where
    function t s opr = case opr of
        ObjectProp op -> ObjectProp $ function t s op
        ObjectInverseOf op -> ObjectInverseOf $ function t s op

instance Function DataRange where
    function t s dra = case dra of
        DataType dt ls -> DataType (function t s dt)
            $ map (\ (cf, rv) -> (function t s cf, function t s rv)) ls
        DataJunction jt drl -> DataJunction jt $ map (function t s) drl
        DataComplementOf dr -> DataComplementOf $ function t s dr
        DataOneOf ll -> DataOneOf $ map (function t s) ll

instance Function ClassExpression where
    function t s cle = case cle of
        Expression c -> Expression $ function t s c
        ObjectJunction jt cel -> ObjectJunction jt $ map (function t s) cel
        ObjectComplementOf ce -> ObjectComplementOf $ function t s ce
        ObjectOneOf il -> ObjectOneOf $ map (function t s) il
        ObjectValuesFrom qt op ce ->
            ObjectValuesFrom qt (function t s op) $ function t s ce
        ObjectHasValue op i -> ObjectHasValue (function t s op) $ function t s i
        ObjectHasSelf op -> ObjectHasSelf $ function t s op
        ObjectCardinality (Cardinality ct i op mce) -> ObjectCardinality
              $ Cardinality ct i (function t s op) $ maybeDo t s mce
        DataValuesFrom qt dp dr -> DataValuesFrom qt
              (function t s dp) $ function t s dr
        DataHasValue dp l -> DataHasValue (function t s dp) $ function t s l
        DataCardinality (Cardinality ct i dp mdr) -> DataCardinality
              $ Cardinality ct i (function t s dp) $ maybeDo t s mdr

instance Function Annotation where
    function t s (Annotation al ap av) = Annotation (map (function t s) al)
          (function t s ap) $ function t s av

instance Function AnnotationValue where
    function t s av = case av of
        AnnValue iri -> AnnValue $ function t s iri
        AnnValLit l -> AnnValLit $ function t s l

instance Function Annotations where
    function t pm = map (function t pm)

instance Function a => Function (AnnotatedList a) where
    function t s = map (\ (ans, a) -> (map (function t s) ans, function t s a))

instance Function Fact where
    function t s f = case f of
        ObjectPropertyFact pn op i ->
            ObjectPropertyFact pn (function t s op) $ function t s i
        DataPropertyFact pn dp l ->
            DataPropertyFact pn (function t s dp) $ function t s l

instance Function ListFrameBit where
    function t s lfb = case lfb of
        AnnotationBit al -> AnnotationBit $ function t s al
        ExpressionBit al -> ExpressionBit $ function t s al
        ObjectBit al -> ObjectBit $ function t s al
        DataBit al -> DataBit $ function t s al
        IndividualSameOrDifferent al ->
            IndividualSameOrDifferent $ function t s al
        DataPropRange al -> DataPropRange $ function t s al
        IndividualFacts al -> IndividualFacts $ function t s al
        _ -> lfb

instance Function AnnFrameBit where
    function t s afb = case afb of
        DatatypeBit dr -> DatatypeBit $ function t s dr
        ClassDisjointUnion cel -> ClassDisjointUnion $ map (function t s) cel
        ClassHasKey opl dpl -> ClassHasKey (map (function t s) opl)
            $ map (function t s) dpl
        ObjectSubPropertyChain opl ->
            ObjectSubPropertyChain $ map (function t s) opl
        _ -> afb

instance Function FrameBit where
    function t s fb = case fb of
        ListFrameBit mr lfb -> ListFrameBit mr $ function t s lfb
        AnnFrameBit ans afb -> AnnFrameBit (function t s ans)
            (function t s afb)

instance Function Extended where
    function t mp ex = case ex of
        Misc ans -> Misc $ function t mp ans
        SimpleEntity e -> SimpleEntity $ function t mp e
        ClassEntity ce -> ClassEntity $ function t mp ce
        ObjectEntity op -> ObjectEntity $ function t mp op

instance Function Frame where
    function t mp (Frame ex fbl) = Frame (function t mp ex)
        (map (function t mp) fbl)

instance Function Axiom where
    function t mp (PlainAxiom ex fb) = PlainAxiom (function t mp ex)
        (function t mp fb)

instance Function Ontology where
  function t mp ( Ontology ouri impList anList f) =
      Ontology (function t mp ouri) (map (function t mp) impList)
         (map (function t mp) anList) (map (function t mp) f)

instance Function OntologyDocument where
  function t mp ( OntologyDocument pm onto) =
      OntologyDocument (function t mp pm) (function t mp onto)
