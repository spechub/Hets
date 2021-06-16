{- |
Module      :  ./OWL2/Extract.hs
Description :  extraction of the sign from the frames
Copyright   :  (c) Francisc-Nicolae Bungiu, Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.bungiu@jacobs-university.de
Stability   :  provisional
Portability :  portable

Extraction of all the entities in the ontology
-}

module OWL2.Extract where

import qualified OWL2.AS as AS
import OWL2.MS
import OWL2.Sign

import Control.Monad
import Common.Lib.State

import Common.IRI

import qualified Data.Set as Set

fromObjPropExpr :: AS.ObjectPropertyExpression -> State Sign ()
fromObjPropExpr = addEntity . AS.mkEntity AS.ObjectProperty . AS.objPropToIRI

fromDataPropExpr :: AS.DataPropertyExpression -> State Sign ()
fromDataPropExpr = addEntity . AS.mkEntity AS.DataProperty

fromIndividual :: AS.Individual -> State Sign ()
fromIndividual ind =  unless (isBlankNode ind) $
 addEntity $ AS.mkEntity AS.NamedIndividual ind

fromAnnoProp :: AS.AnnotationProperty -> State Sign ()
fromAnnoProp = addEntity . AS.mkEntity AS.AnnotationProperty

fromLiteral :: AS.Literal -> State Sign ()
fromLiteral l = case l of
    AS.Literal _ ty -> case ty of
        AS.Typed u -> addEntity $ AS.mkEntity AS.Datatype u
        _ -> return ()
    _ -> return ()

fromDType :: AS.Datatype -> State Sign ()
fromDType dt = unless (AS.isDatatypeKey dt) $ addEntity $ AS.mkEntity AS.Datatype dt

-- | Adds the DataRange to the Signature and returns it as a State Sign ()
fromDataRange :: AS.DataRange -> State Sign ()
fromDataRange dr = case dr of
  AS.DataJunction _ lst -> mapM_ fromDataRange lst
  AS.DataComplementOf r -> fromDataRange r
  AS.DataOneOf cs -> mapM_ fromLiteral cs
  AS.DataType r fcs -> do
    fromDType r
    mapM_ (fromLiteral . snd) fcs

-- | Adds the Fact to the Signature and returns it as a State Sign()
fromFact :: Fact -> State Sign ()
fromFact f = case f of
  ObjectPropertyFact _ obe ind -> do
      fromObjPropExpr obe
      fromIndividual ind
  DataPropertyFact _ dpe _ ->
      fromDataPropExpr dpe

-- | Adds the Description to the Signature. Returns it as a State
fromDescription :: AS.ClassExpression -> State Sign ()
fromDescription desc = case desc of
  AS.Expression u ->
      unless (AS.isThing u) $ addEntity $ AS.mkEntity AS.Class u
  AS.ObjectJunction _ ds -> mapM_ fromDescription ds
  AS.ObjectComplementOf d -> fromDescription d
  AS.ObjectOneOf is -> mapM_ fromIndividual is
  AS.ObjectValuesFrom _ opExpr d -> do
    fromObjPropExpr opExpr
    fromDescription d
  AS.ObjectHasSelf opExpr -> fromObjPropExpr opExpr
  AS.ObjectHasValue opExpr i -> do
    fromObjPropExpr opExpr
    fromIndividual i
  AS.ObjectCardinality (AS.Cardinality _ _ opExpr md) -> do
    fromObjPropExpr opExpr
    maybe (return ()) fromDescription md
  AS.DataValuesFrom _ dExp r -> do
    fromDataPropExpr (head dExp)
    fromDataRange r
  AS.DataHasValue dExp c -> do
    fromDataPropExpr dExp
    fromLiteral c
  AS.DataCardinality (AS.Cardinality _ _ dExp mr) -> do
    fromDataPropExpr dExp
    maybe (return ()) fromDataRange mr

fromAnno :: AS.Annotation -> State Sign ()
fromAnno (AS.Annotation as apr _) = do
    fromAnnoProp apr
    fromAnnos as

fromAnnos :: Annotations -> State Sign ()
fromAnnos = mapM_ fromAnno

fromAnnoList :: (a -> State Sign ()) -> AnnotatedList a -> State Sign ()
fromAnnoList f al = do
    fromAnnos $ concatMap fst al
    mapM_ (f . snd) al

{- | Adds possible ListFrameBits to the Signature by calling
bottom level functions -}
fromLFB :: Maybe AS.Relation -> ListFrameBit -> State Sign ()
fromLFB r lfb = case lfb of
    AnnotationBit ab ->
      unless (r `elem` [Just (AS.DRRelation AS.ADomain), Just (AS.DRRelation AS.ARange)])
        $ fromAnnoList fromAnnoProp ab
    ExpressionBit al -> fromAnnoList fromDescription al
    ObjectBit anob -> fromAnnoList fromObjPropExpr anob
    DataBit dlst -> fromAnnoList fromDataPropExpr dlst
    IndividualSameOrDifferent anind -> fromAnnoList fromIndividual anind
    ObjectCharacteristics al -> fromAnnos $ concatMap fst al
    DataPropRange dr -> fromAnnoList fromDataRange dr
    IndividualFacts fct -> fromAnnoList fromFact fct

fromAFB :: AnnFrameBit -> State Sign ()
fromAFB afb = case afb of
    AnnotationFrameBit _ -> return ()
    DataFunctional -> return ()
    DatatypeBit dr -> fromDataRange dr
    ClassDisjointUnion cls -> mapM_ fromDescription cls
    ClassHasKey obe dpe -> do
      mapM_ fromObjPropExpr obe
      mapM_ fromDataPropExpr dpe
    ObjectSubPropertyChain ope -> mapM_ fromObjPropExpr ope

{- | Calls the completion of Signature based on
case separation of ListFrameBit and AnnotationFrameBit -}
fromFB :: Extended -> FrameBit -> State Sign ()
fromFB ext fb = case fb of
  ListFrameBit rel lfb -> do
    fromExt ext
    fromLFB rel lfb
  AnnFrameBit an anf -> do
    fromAnnos an
    fromAFB anf
    case anf of
        AnnotationFrameBit Assertion -> case ext of
            Misc _ -> return ()
            _ -> fromExt ext
        _ -> fromExt ext

fromFrame :: Frame -> State Sign ()
fromFrame (Frame ex fblist) = mapM_ (fromFB ex) fblist

fromExt :: Extended -> State Sign ()
fromExt ext = case ext of
    SimpleEntity e -> addEntity e
    ObjectEntity op -> fromObjPropExpr op
    ClassEntity ce -> fromDescription ce
    Misc ans -> fromAnnos ans

{- | Top level function: takes the OntologyDocument and completes
the signature by calling completeSignForFrame -}
extractSign :: OntologyDocument -> State Sign ()
extractSign = mapM_ fromFrame . ontFrames . ontology

toDecl :: Sign -> [Frame]
toDecl s =
    let cls = map (AS.mkEntity AS.Class) $ Set.toList (concepts s)
        dt = map (AS.mkEntity AS.Datatype) $ Set.toList (datatypes s)
        op = map (AS.mkEntity AS.ObjectProperty) $ Set.toList (objectProperties s)
        dp = map (AS.mkEntity AS.DataProperty) $ Set.toList (dataProperties s)
        i = map (AS.mkEntity AS.NamedIndividual) $ Set.toList (individuals s)
        ans = map (AS.mkEntity AS.AnnotationProperty) $ Set.toList (annotationRoles s)
    in map (\ c -> Frame (mkExtendedEntity c)
        [AnnFrameBit [] $ AnnotationFrameBit Declaration])
            (cls ++ dt ++ op ++ dp ++ i ++ ans)

signToFrames :: [Frame] -> [Frame]
signToFrames f = let s = mapM_ fromFrame f in toDecl $ execState s emptySign
