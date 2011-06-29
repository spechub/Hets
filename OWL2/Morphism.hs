{- |
Module      :  $Header$
Description :  OWL Morphisms
Copyright   :  (c) Dominik Luecke, 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Morphisms for OWL
-}

module OWL2.Morphism
  ( OWLMorphism (..)
  , isOWLInclusion
  , inclOWLMorphism
  , legalMor
  , composeMor
  , cogeneratedSign
  , generatedSign
  , matchesSym
  , statSymbItems
  , statSymbMapItems
  , inducedFromMor
  , symMapOf
  , mapSen
  ) where

import OWL2.AS
import OWL2.FunctionalPrint ()
import OWL2.Sign
import OWL2.StaticAnalysis
import OWL2.FS
import OWL2.Symbols

import Common.DocUtils
import Common.Doc
import Common.Result
import Common.Lib.State (execState)
import Common.Lib.Rel (setToMap)

import Control.Monad
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

data OWLMorphism = OWLMorphism
  { osource :: Sign
  , otarget :: Sign
  , mmaps :: Map.Map Entity IRI
  } deriving (Show, Eq, Ord)

inclOWLMorphism :: Sign -> Sign -> OWLMorphism
inclOWLMorphism s t = OWLMorphism
 { osource = s
 , otarget = t
 , mmaps = Map.empty }

isOWLInclusion :: OWLMorphism -> Bool
isOWLInclusion m = Map.null (mmaps m) && isSubSign (osource m) (otarget m)

symMap :: Map.Map Entity IRI -> Map.Map Entity Entity
symMap = Map.mapWithKey (\ (Entity ty _) -> Entity ty)

inducedElems :: Map.Map Entity IRI -> [Entity]
inducedElems = Map.elems . symMap

inducedSign :: Map.Map Entity IRI -> Sign -> Sign
inducedSign m = execState $ do
    mapM_ (modEntity Set.delete) $ Map.keys m
    mapM_ (modEntity Set.insert) $ inducedElems m

inducedFromMor :: Map.Map RawSymb RawSymb -> Sign -> Result OWLMorphism
inducedFromMor rm sig = do
  let syms = symOf sig
  mm <- foldM (\ m p -> case p of
        (ASymbol s@(Entity _ v), ASymbol (Entity _ u)) ->
            if Set.member s syms
            then return $ if u == v then m else Map.insert s u m
            else fail $ "unknown symbol: " ++ showDoc s "\n" ++ shows sig ""
        (AnUri v, AnUri u) -> case filter (`Set.member` syms)
          $ map (`Entity` v) entityTypes of
          [] -> fail $ "unknown symbol: " ++ showDoc v "\n" ++ shows sig ""
          l -> return $ if u == v then m else foldr (`Map.insert` u) m l
        _ -> error "OWL2.Morphism.inducedFromMor") Map.empty $ Map.toList rm
  return OWLMorphism
    { osource = sig
    , otarget = inducedSign mm sig
    , mmaps = mm }

symMapOf :: OWLMorphism -> Map.Map Entity Entity
symMapOf mor = Map.union (symMap $ mmaps mor) $ setToMap $ symOf $ osource mor

instance Pretty OWLMorphism where
  pretty m = let
    s = osource m
    srcD = specBraces $ space <> pretty s
    t = otarget m
    in if isOWLInclusion m then
           if isSubSign t s then
              fsep [text "identity morphism over", srcD]
           else fsep
             [ text "inclusion morphism of"
             , srcD
             , text "extended with"
             , pretty $ Set.difference (symOf t) $ symOf s ]
       else fsep
         [ pretty $ mmaps m
         , colon <+> srcD, mapsto <+> specBraces (space <> pretty t) ]

legalMor :: OWLMorphism -> Bool
legalMor m = let mm = mmaps m in
  Set.isSubsetOf (Map.keysSet mm) (symOf $ osource m)
  && Set.isSubsetOf (Set.fromList $ inducedElems mm) (symOf $ otarget m)

getIri :: EntityType -> IRI -> Map.Map Entity IRI -> IRI
getIri ty u = fromMaybe u . Map.lookup (Entity ty u)

composeMor :: OWLMorphism -> OWLMorphism -> Result OWLMorphism
composeMor m1 m2 =
  let nm = Set.fold (\ s@(Entity ty u) -> let
            t = getIri ty u $ mmaps m1
            r = getIri ty t $ mmaps m2
            in if r == u then id else Map.insert s r) Map.empty
           . symOf $ osource m1
  in return m1
     { otarget = otarget m2
     , mmaps = nm }

cogeneratedSign :: Set.Set Entity -> Sign -> Result OWLMorphism
cogeneratedSign s sign =
  let sig2 = execState (mapM_ (modEntity Set.delete) $ Set.toList s) sign
  in if isSubSign sig2 sign then return $ inclOWLMorphism sig2 sign else
         fail "non OWL2 subsignatures for (co)generatedSign"

generatedSign :: Set.Set Entity -> Sign -> Result OWLMorphism
generatedSign s sign = cogeneratedSign (Set.difference (symOf sign) s) sign

matchesSym :: Entity -> RawSymb -> Bool
matchesSym e@(Entity _ u) r = case r of
  ASymbol s -> s == e
  AnUri s -> s == u

statSymbItems :: [SymbItems] -> [RawSymb]
statSymbItems = concatMap
  $ \ (SymbItems m us) -> case m of
               Nothing -> map AnUri us
               Just ty -> map (ASymbol . Entity ty) us

statSymbMapItems :: [SymbMapItems] -> Result (Map.Map RawSymb RawSymb)
statSymbMapItems =
  foldM (\ m (s, t) -> case Map.lookup s m of
    Nothing -> return $ Map.insert s t m
    Just u -> case (u, t) of
      (AnUri su, ASymbol (Entity _ tu)) | su == tu ->
        return $ Map.insert s t m
      (ASymbol (Entity _ su), AnUri tu) | su == tu ->
        return m
      _ -> if u == t then return m else
        fail $ "differently mapped symbol: " ++ showDoc s "\nmapped to "
             ++ showDoc u " and " ++ showDoc t "")
  Map.empty
  . concatMap (\ (SymbMapItems m us) ->
      let ps = map (\ (u, v) -> (u, fromMaybe u v)) us in
      case m of
        Nothing -> map (\ (s, t) -> (AnUri s, AnUri t)) ps
        Just ty -> let mS = ASymbol . Entity ty in
                   map (\ (s, t) -> (mS s, mS t)) ps)

mapAnno :: Map.Map Entity IRI -> Annotation -> Annotation
mapAnno m ann = case ann of
  Annotation l a e -> Annotation l (getIri AnnotationProperty a m) e

mapSen :: OWLMorphism -> Axiom -> Result Axiom
mapSen m = return . mapAxiom (mmaps m)

mapAxiom :: Map.Map Entity IRI -> Axiom -> Axiom
mapAxiom m axm = case axm of
  PlainAxiom as a -> PlainAxiom (map (mapAnno m) as) $ mapPlainAxiom m a
    
mapObjExpr :: Map.Map Entity IRI -> ObjectPropertyExpression
           -> ObjectPropertyExpression
mapObjExpr m ope = case ope of
  ObjectProp u -> ObjectProp $ getIri ObjectProperty u m
  ObjectInverseOf o -> ObjectInverseOf $ mapObjExpr m o

mapDRange :: Map.Map Entity IRI -> DataRange -> DataRange
mapDRange m dr = case dr of
    DataType u l -> DataType (getIri Datatype u m) l
    DataJunction j l -> DataJunction j (map (mapDRange m) l)
    DataComplementOf d -> DataComplementOf $ mapDRange m d
    DataOneOf _ -> dr

mapDataExpr :: Map.Map Entity IRI -> DataPropertyExpression
            -> DataPropertyExpression
mapDataExpr m dpe = getIri DataProperty dpe m

getClassIri :: IRI -> Map.Map Entity IRI -> IRI
getClassIri = getIri Class

getIndIri :: IRI -> Map.Map Entity IRI -> IRI
getIndIri = getIri NamedIndividual

mapCard :: (a -> b) -> (c -> d) -> Cardinality a c -> Cardinality b d
mapCard f g (Cardinality ty i a mb) =
  Cardinality ty i (f a) $ fmap g mb

mapDescr :: Map.Map Entity IRI -> ClassExpression -> ClassExpression
mapDescr m desc = case desc of
    Expression u -> Expression $ getClassIri u m
    ObjectJunction ty ds -> ObjectJunction ty $ map (mapDescr m) ds
    ObjectComplementOf d -> ObjectComplementOf $ mapDescr m d
    ObjectOneOf is -> ObjectOneOf $ map (`getIndIri` m) is
    ObjectValuesFrom ty o d -> ObjectValuesFrom ty (mapObjExpr m o)
      $ mapDescr m d
    ObjectHasSelf o -> ObjectHasSelf $ mapObjExpr m o
    ObjectHasValue o i -> ObjectHasValue (mapObjExpr m o) $ getIndIri i m
    ObjectCardinality c -> ObjectCardinality
      $ mapCard (mapObjExpr m) (mapDescr m) c
    DataValuesFrom ty d ds dr -> DataValuesFrom ty (mapDataExpr m d)
      (map (mapDataExpr m) ds) $ mapDRange m dr
    DataHasValue d c -> DataHasValue (mapDataExpr m d) c
    DataCardinality c -> DataCardinality
       $ mapCard (mapDataExpr m) (mapDRange m) c

mapSubObjExpr :: Map.Map Entity IRI -> SubObjectPropertyExpression
              -> SubObjectPropertyExpression
mapSubObjExpr m ope = case ope of
  OPExpression o -> OPExpression $ mapObjExpr m o
  SubObjectPropertyChain os -> SubObjectPropertyChain
    $ map (mapObjExpr m) os

mapDataDomOrRange :: Map.Map Entity IRI -> DataDomainOrRange
                  -> DataDomainOrRange
mapDataDomOrRange m ddr = case ddr of
  DataDomain d -> DataDomain $ mapDescr m d
  DataRange d -> DataRange $ mapDRange m d

mapAssertion :: Map.Map Entity IRI -> (a -> b) -> (c -> d)
             -> Assertion a c -> Assertion b d
mapAssertion m f g (Assertion a ty i b) =
  Assertion (f a) ty (getIndIri i m) $ g b

mapPlainAxiom :: Map.Map Entity IRI -> PlainAxiom -> PlainAxiom
mapPlainAxiom m pax = case pax of
    AnnotationAssertion ir -> AnnotationAssertion ir
    AnnotationAxiom rel p ir -> AnnotationAxiom rel (getIri AnnotationProperty p m) ir
    SubClassOf s t -> SubClassOf (mapDescr m s) $ mapDescr m t
    EquivOrDisjointClasses ty ds -> EquivOrDisjointClasses ty
      $ map (mapDescr m) ds
    DisjointUnion u ds -> DisjointUnion (getClassIri u m)
      $ map (mapDescr m) ds
    SubObjectPropertyOf so o -> SubObjectPropertyOf (mapSubObjExpr m so)
      $ mapObjExpr m o
    EquivOrDisjointObjectProperties ty os -> EquivOrDisjointObjectProperties ty
      $ map (mapObjExpr m) os
    ObjectPropertyDomainOrRange odr o d -> ObjectPropertyDomainOrRange odr
      (mapObjExpr m o) $ mapDescr m d
    InverseObjectProperties o p -> InverseObjectProperties (mapObjExpr m o)
      $ mapObjExpr m p
    ObjectPropertyCharacter c o -> ObjectPropertyCharacter c $ mapObjExpr m o
    SubDataPropertyOf d e -> SubDataPropertyOf (mapDataExpr m d)
      $ mapDataExpr m e
    EquivOrDisjointDataProperties ty ds -> EquivOrDisjointDataProperties ty
      $ map (mapDataExpr m) ds
    DataPropertyDomainOrRange dd d -> DataPropertyDomainOrRange
      (mapDataDomOrRange m dd) $ mapDataExpr m d
    FunctionalDataProperty d -> FunctionalDataProperty $ mapDataExpr m d
    SameOrDifferentIndividual ty is -> SameOrDifferentIndividual ty $ map (`getIndIri` m) is
    ClassAssertion d i -> ClassAssertion (mapDescr m d) $ getIndIri i m
    ObjectPropertyAssertion a -> ObjectPropertyAssertion
      $ mapAssertion m (mapObjExpr m) (`getIndIri` m) a
    DataPropertyAssertion a -> DataPropertyAssertion
      $ mapAssertion m (mapDataExpr m) id a
    Declaration (Entity ty u) -> Declaration $ Entity ty $ getIri ty u m
    DatatypeDefinition ty d-> DatatypeDefinition (getIri Datatype ty m) (mapDRange m d)
    HasKey c ob da-> HasKey (mapDescr m c) (map (mapObjExpr m) ob) (map (mapDataExpr m) da)
