{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

{- |
Module      :  ./OWL2/Function.hs
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Instances for some of the functions used in OWL 2
-}

module OWL2.Function where

import qualified OWL2.AS as AS
import Common.IRI
import Common.Id (stringToId)
import OWL2.MS
import OWL2.Sign
import OWL2.Symbols

import Data.List (stripPrefix)
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

{- | this class contains general functions which operate on the ontology
    document, such as prefix renaming, IRI expansion or Morphism mapping -}
class Function a where
    function :: Action -> AMap -> a -> a

data Action = Rename | Expand
    deriving (Show, Eq, Ord)

type StringMap = Map.Map String String
type MorphMap = Map.Map AS.Entity IRI

data AMap =
      StringMap StringMap
    | MorphMap MorphMap
    deriving (Show, Eq, Ord)

maybeDo :: (Function a) => Action -> AMap -> Maybe a -> Maybe a
maybeDo t mp = fmap $ function t mp

getIri :: AS.EntityType -> IRI -> Map.Map AS.Entity IRI -> IRI
getIri ty u = fromMaybe u . Map.lookup (AS.mkEntity ty u)

cutWith :: AS.EntityType -> Action -> AMap -> IRI -> IRI
cutWith ty t s anIri = AS.cutIRI $ function t s $ AS.mkEntity ty anIri

err :: t
err = error "operation not allowed"

instance Function AS.PrefixMap where
    function a m oldPs = case m of
        StringMap mp -> case a of
            Rename ->
                foldl (\ ns (pre, ouri) ->
                    Map.insert (Map.findWithDefault pre pre mp) ouri ns)
                    Map.empty $ Map.toList oldPs
            Expand -> oldPs
        _ -> err

instance Function IRI where
  function a m iri = case m of
    StringMap pm -> case a of
     Rename -> let pre = prefixName iri in
              iri { prefixName = Map.findWithDefault pre pre pm}
     Expand ->
      let np = prefixName iri
          lp = show $ iriPath iri
          iRi = if hasFullIRI iri then let
                  ex = np ++ ":" ++ lp
                  res = let x = expandCurie (Map.map mkIRI pm) iri in
                         case x of
                          Just y -> y
                          Nothing -> error $ "could not expand:" ++ showIRI iri 
                in if elem np ["http", "https"] then -- abbreviate
                        case Map.lookup "" pm of
                          Just ep | length ep > 5 -> case stripPrefix ep ex of
                            Just rl@(_ : _) -> res
                              { prefixName = ""
                              , iriPath = stringToId rl -- todo: maybe we should keep the Id structure of iriPath iri. See #1820
                              }
                            _ -> res
                          _ -> res
                      else res
               else if isBlankNode iri then iri else   
                    let iriMap = foldl (\pm' (kp, vp) -> 
                                case parseIRI vp of
                                  Just i -> Map.insert kp i pm'
                                  Nothing -> if null kp then 
                                               Map.insert kp 
                                                 ((mkIRI vp)) 
                                                 pm'
                                              else pm') 
                              Map.empty $  
                              Map.toList $ Map.union pm AS.predefPrefixes
                        x = expandCurie iriMap iri 
                    in case x of
                        Just y -> y
                        Nothing -> error $ "could not expand curie:" ++ showIRI iri
      in AS.setReservedPrefix iRi
    _ -> iri

instance Function Sign where
   function t mp (Sign p1 p2 p3 p4 p5 p6 p7 p8) = case mp of
    StringMap _ ->
        Sign (Set.map (function t mp) p1)
            (Set.map (function t mp) p2)
            (Set.map (function t mp) p3)
            (Set.map (function t mp) p4)
            (Set.map (function t mp) p5)
            (Set.map (function t mp) p6)
            (Map.mapKeys (function t mp) p7)
            (function t mp p8)
    _ -> err

instance Function AS.Entity where
    function t pm (AS.Entity _ ty ent) = case pm of
        StringMap _ -> AS.mkEntity ty $ function t pm ent
        MorphMap m -> AS.mkEntity ty $ getIri ty ent m

instance Function AS.Literal where
    function t pm l = case l of
        AS.Literal lf (AS.Typed dt) -> AS.Literal lf $ AS.Typed
                $ cutWith AS.Datatype t pm dt
        _ -> l

instance Function AS.ObjectPropertyExpression where
    function t s opr = case opr of
        AS.ObjectProp op -> AS.ObjectProp $ cutWith AS.ObjectProperty t s op
        AS.ObjectInverseOf op -> AS.ObjectInverseOf $ function t s op

instance Function AS.DataRange where
    function t s dra = case dra of
        AS.DataType dt ls -> AS.DataType (cutWith AS.Datatype t s dt)
            $ map (\ (cf, rv) -> (function t s cf, function t s rv)) ls
        AS.DataJunction jt drl -> AS.DataJunction jt $ map (function t s) drl
        AS.DataComplementOf dr -> AS.DataComplementOf $ function t s dr
        AS.DataOneOf ll -> AS.DataOneOf $ map (function t s) ll

instance Function AS.ClassExpression where
    function t s cle = case cle of
        AS.Expression c -> AS.Expression $ cutWith AS.Class t s c
        AS.ObjectJunction jt cel -> AS.ObjectJunction jt $ map (function t s) cel
        AS.ObjectComplementOf ce -> AS.ObjectComplementOf $ function t s ce
        AS.ObjectOneOf il -> AS.ObjectOneOf $ map (cutWith AS.NamedIndividual t s) il
        AS.ObjectValuesFrom qt op ce ->
            AS.ObjectValuesFrom qt (function t s op) $ function t s ce
        AS.ObjectHasValue op i -> AS.ObjectHasValue (function t s op)
            $ cutWith AS.NamedIndividual t s i
        AS.ObjectHasSelf op -> AS.ObjectHasSelf $ function t s op
        AS.ObjectCardinality (AS.Cardinality ct i op mce) -> AS.ObjectCardinality
            $ AS.Cardinality ct i (function t s op) $ maybeDo t s mce
        AS.DataValuesFrom qt dp dr -> AS.DataValuesFrom qt
            [(cutWith AS.DataProperty t s (head dp))] $ function t s dr
        AS.DataHasValue dp l -> AS.DataHasValue (cutWith AS.DataProperty t s dp)
            $ function t s l
        AS.DataCardinality (AS.Cardinality ct i dp mdr) -> AS.DataCardinality
              $ AS.Cardinality ct i (cutWith AS.DataProperty t s dp) $ maybeDo t s mdr

instance Function AS.Annotation where
    function t s (AS.Annotation al ap av) = AS.Annotation (map (function t s) al)
        (cutWith AS.AnnotationProperty t s ap) $ function t s av

instance Function AS.AnnotationValue where
    function t s av = case av of
        AS.AnnValue anIri -> AS.AnnValue $ function t s anIri
        AS.AnnValLit l -> AS.AnnValLit $ function t s l

instance Function Annotations where
    function t pm = map (function t pm)

-- | only for non-IRI AnnotatedLists
instance Function a => Function (AnnotatedList a) where
    function t s = map (\ (ans, a) -> (map (function t s) ans, function t s a))

-- | only for IRI AnnotatedLists
mapAnnList :: AS.EntityType -> Action -> AMap -> AnnotatedList IRI
    -> AnnotatedList IRI
mapAnnList ty t m anl =
    let ans = map fst anl
        l = map snd anl
    in zip (map (function t m) ans) $ map (cutWith ty t m) l

instance Function Fact where
    function t s f = case f of
        ObjectPropertyFact pn op i -> ObjectPropertyFact pn
            (function t s op) $ cutWith AS.NamedIndividual t s i
        DataPropertyFact pn dp l -> DataPropertyFact pn
            (cutWith AS.DataProperty t s dp) $ function t s l

instance Function ListFrameBit where
    function t s lfb = case lfb of
        AnnotationBit al -> AnnotationBit $ mapAnnList AS.AnnotationProperty t s al
        ExpressionBit al -> ExpressionBit $ function t s al
        ObjectBit al -> ObjectBit $ function t s al
        DataBit al -> DataBit $ mapAnnList AS.DataProperty t s al
        IndividualSameOrDifferent al ->
            IndividualSameOrDifferent $ mapAnnList AS.NamedIndividual t s al
        DataPropRange al -> DataPropRange $ function t s al
        IndividualFacts al -> IndividualFacts $ function t s al
        _ -> lfb

instance Function AnnFrameBit where
    function t s afb = case afb of
        DatatypeBit dr -> DatatypeBit $ function t s dr
        ClassDisjointUnion cel -> ClassDisjointUnion $ map (function t s) cel
        ClassHasKey opl dpl -> ClassHasKey (map (function t s) opl)
            $ map (cutWith AS.DataProperty t s) dpl
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
        SimpleEntity ent -> SimpleEntity $ function t mp ent
        ClassEntity ce -> ClassEntity $ function t mp ce
        ObjectEntity op -> ObjectEntity $ function t mp op

instance Function Frame where
    function t mp (Frame ex fbl) = Frame (function t mp ex)
        (map (function t mp) fbl)

instance Function Axiom where
    function t mp (PlainAxiom ex fb) = PlainAxiom (function t mp ex)
        (function t mp fb)

instance Function Ontology where
  function t mp (Ontology ouri impList anList f) =
      Ontology (function t mp ouri) (map (function t mp) impList)
         (map (function t mp) anList) (map (function t mp) f)

instance Function OntologyDocument where
  function t mp (OntologyDocument pm onto) =
      OntologyDocument (function t mp pm) (function t mp onto)

instance Function RawSymb where
  function t mp rs = case rs of
     ASymbol e -> ASymbol $ function t mp e
     AnUri i -> AnUri $ function t mp i
     p -> p
