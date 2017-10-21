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

import OWL2.AS
import Common.IRI
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
type MorphMap = Map.Map Entity IRI

data AMap =
      StringMap StringMap
    | MorphMap MorphMap
    deriving (Show, Eq, Ord)

maybeDo :: (Function a) => Action -> AMap -> Maybe a -> Maybe a
maybeDo t mp = fmap $ function t mp

getIri :: EntityType -> IRI -> Map.Map Entity IRI -> IRI
getIri ty u = fromMaybe u . Map.lookup (mkEntity ty u)

cutWith :: EntityType -> Action -> AMap -> IRI -> IRI
cutWith ty t s anIri= cutIRI $ function t s $ mkEntity ty anIri

err :: t
err = error "operation not allowed"

instance Function PrefixMap where
    function a m oldPs = case m of
        StringMap mp -> case a of
            Rename ->
                foldl (\ ns (pre, ouri) ->
                    Map.insert (Map.findWithDefault pre pre mp) ouri ns)
                    Map.empty $ Map.toList oldPs
            Expand -> oldPs
        _ -> err

instance Function IRI where
  function a m qn = case m of
    StringMap pm -> case a of
     Rename -> let pre = prefixName qn in
              qn { prefixName = Map.findWithDefault pre pre pm}
     Expand ->
      let np = prefixName qn
          lp = abbrevPath qn
          iRi = if hasFullIRI qn then let
                  ex = np ++ ":" ++ lp
                  res = let x = expandCurie (Map.map mkIRI pm) qn in
                         case x of
                          Just y -> y
                          Nothing -> error $ "could not expand:" ++ showIRI qn 
                in if elem np ["http", "https"] then -- abbreviate
                        case Map.lookup "" pm of
                          Just ep | length ep > 5 -> case stripPrefix ep ex of
                            Just rl@(_ : _) -> res
                              { prefixName = ""
                              , abbrevPath = rl
                              }
                            _ -> res
                          _ -> res
                      else res
               else let iriMap = foldl (\pm' (kp, vp) -> 
                                case parseIRI vp of
                                  Just i -> Map.insert kp i pm'
                                  Nothing -> if null kp then 
                                               Map.insert kp 
                                                 ((mkIRI vp)) 
                                                 pm'
                                              else pm') 
                              Map.empty $  
                              Map.toList $ Map.union pm predefPrefixes
                        x = expandCurie iriMap qn 
                    in case x of
                        Just y -> y
                        Nothing -> error $ "could not expand curie:" ++ showIRI qn
      in setReservedPrefix iRi
    _ -> qn

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

instance Function Entity where
    function t pm (Entity _ ty ent) = case pm of
        StringMap _ -> mkEntity ty $ function t pm ent
        MorphMap m -> mkEntity ty $ getIri ty ent m

instance Function Literal where
    function t pm l = case l of
        Literal lf (Typed dt) -> Literal lf $ Typed
                $ cutWith Datatype t pm dt
        _ -> l

instance Function ObjectPropertyExpression where
    function t s opr = case opr of
        ObjectProp op -> ObjectProp $ cutWith ObjectProperty t s op
        ObjectInverseOf op -> ObjectInverseOf $ function t s op

instance Function DataRange where
    function t s dra = case dra of
        DataType dt ls -> DataType (cutWith Datatype t s dt)
            $ map (\ (cf, rv) -> (function t s cf, function t s rv)) ls
        DataJunction jt drl -> DataJunction jt $ map (function t s) drl
        DataComplementOf dr -> DataComplementOf $ function t s dr
        DataOneOf ll -> DataOneOf $ map (function t s) ll

instance Function ClassExpression where
    function t s cle = case cle of
        Expression c -> Expression $ cutWith Class t s c
        ObjectJunction jt cel -> ObjectJunction jt $ map (function t s) cel
        ObjectComplementOf ce -> ObjectComplementOf $ function t s ce
        ObjectOneOf il -> ObjectOneOf $ map (cutWith NamedIndividual t s) il
        ObjectValuesFrom qt op ce ->
            ObjectValuesFrom qt (function t s op) $ function t s ce
        ObjectHasValue op i -> ObjectHasValue (function t s op)
            $ cutWith NamedIndividual t s i
        ObjectHasSelf op -> ObjectHasSelf $ function t s op
        ObjectCardinality (Cardinality ct i op mce) -> ObjectCardinality
            $ Cardinality ct i (function t s op) $ maybeDo t s mce
        DataValuesFrom qt dp dr -> DataValuesFrom qt
            (cutWith DataProperty t s dp) $ function t s dr
        DataHasValue dp l -> DataHasValue (cutWith DataProperty t s dp)
            $ function t s l
        DataCardinality (Cardinality ct i dp mdr) -> DataCardinality
              $ Cardinality ct i (cutWith DataProperty t s dp) $ maybeDo t s mdr

instance Function Annotation where
    function t s (Annotation al ap av) = Annotation (map (function t s) al)
        (cutWith AnnotationProperty t s ap) $ function t s av

instance Function AnnotationValue where
    function t s av = case av of
        AnnValue anIri -> AnnValue $ function t s anIri
        AnnValLit l -> AnnValLit $ function t s l

instance Function Annotations where
    function t pm = map (function t pm)

-- | only for non-IRI AnnotatedLists
instance Function a => Function (AnnotatedList a) where
    function t s = map (\ (ans, a) -> (map (function t s) ans, function t s a))

-- | only for IRI AnnotatedLists
mapAnnList :: EntityType -> Action -> AMap -> AnnotatedList IRI
    -> AnnotatedList IRI
mapAnnList ty t m anl =
    let ans = map fst anl
        l = map snd anl
    in zip (map (function t m) ans) $ map (cutWith ty t m) l

instance Function Fact where
    function t s f = case f of
        ObjectPropertyFact pn op i -> ObjectPropertyFact pn
            (function t s op) $ cutWith NamedIndividual t s i
        DataPropertyFact pn dp l -> DataPropertyFact pn
            (cutWith DataProperty t s dp) $ function t s l

instance Function ListFrameBit where
    function t s lfb = case lfb of
        AnnotationBit al -> AnnotationBit $ mapAnnList AnnotationProperty t s al
        ExpressionBit al -> ExpressionBit $ function t s al
        ObjectBit al -> ObjectBit $ function t s al
        DataBit al -> DataBit $ mapAnnList DataProperty t s al
        IndividualSameOrDifferent al ->
            IndividualSameOrDifferent $ mapAnnList NamedIndividual t s al
        DataPropRange al -> DataPropRange $ function t s al
        IndividualFacts al -> IndividualFacts $ function t s al
        _ -> lfb

instance Function AnnFrameBit where
    function t s afb = case afb of
        DatatypeBit dr -> DatatypeBit $ function t s dr
        ClassDisjointUnion cel -> ClassDisjointUnion $ map (function t s) cel
        ClassHasKey opl dpl -> ClassHasKey (map (function t s) opl)
            $ map (cutWith DataProperty t s) dpl
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
