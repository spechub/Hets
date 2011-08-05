{- |
Module      :  $Header$
Description :  extraction of the sign from the frames
Copyright   :  (c) Francisc-Nicolae Bungiu, Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.bungiu@jacobs-university.de
Stability   :  provisional
Portability :  portable

Extraction of all the entities in the ontology
-}

module OWL2.Extract where

import OWL2.AS
import OWL2.MS
import OWL2.Sign
import OWL2.StaticAnalysis

import Control.Monad
import Common.Lib.State

import qualified Data.Set as Set

addObjPropExpr :: ObjectPropertyExpression -> State Sign ()
addObjPropExpr = addEntity . Entity ObjectProperty . objPropToIRI

addDataPropExpr :: DataPropertyExpression -> State Sign ()
addDataPropExpr = addEntity . Entity DataProperty

addIndividual :: Individual -> State Sign ()
addIndividual ind =
    unless (iriType ind == NodeID) $ addEntity $ Entity NamedIndividual ind

addAnnoProp :: AnnotationProperty -> State Sign ()
addAnnoProp = addEntity . Entity AnnotationProperty

addLiteral :: Literal -> State Sign ()
addLiteral l = case l of
    Literal _ ty -> case ty of
        Typed u -> addEntity $ Entity Datatype u
        _ -> return ()
    _ -> return ()

addDType :: Datatype -> State Sign ()
addDType dt = unless (isDatatypeKey dt) $ addEntity $ Entity Datatype dt

-- | Adds the DataRange to the Signature and returns it as a State Sign ()
addDataRange :: DataRange -> State Sign ()
addDataRange dr = case dr of
  DataJunction _ lst -> mapM_ addDataRange lst
  DataComplementOf r -> addDataRange r
  DataOneOf cs -> mapM_ addLiteral cs
  DataType r fcs -> do
    addDType r
    mapM_ (addLiteral . snd) fcs

-- | Adds the Fact to the Signature and returns it as a State Sign()
addFact :: Fact -> State Sign ()
addFact f = case f of
  ObjectPropertyFact _ obe ind -> do
      addObjPropExpr obe
      addIndividual ind
  DataPropertyFact _ dpe _ ->
      addDataPropExpr dpe

-- | Adds the Description to the Signature. Returns it as a State
addDescription :: ClassExpression -> State Sign ()
addDescription desc = case desc of
  Expression u ->
      unless (isThing u) $ addEntity $ Entity Class u
  ObjectJunction _ ds -> mapM_ addDescription ds
  ObjectComplementOf d -> addDescription d
  ObjectOneOf is -> mapM_ addIndividual is
  ObjectValuesFrom _ opExpr d -> do
    addObjPropExpr opExpr
    addDescription d
  ObjectHasSelf opExpr -> addObjPropExpr opExpr
  ObjectHasValue opExpr i -> do
    addObjPropExpr opExpr
    addIndividual i
  ObjectCardinality (Cardinality _ _ opExpr md) -> do
    addObjPropExpr opExpr
    maybe (return ()) addDescription md
  DataValuesFrom _ dExp r -> do
    addDataPropExpr dExp
    addDataRange r
  DataHasValue dExp c -> do
    addDataPropExpr dExp
    addLiteral c
  DataCardinality (Cardinality _ _ dExp mr) -> do
    addDataPropExpr dExp
    maybe (return ()) addDataRange mr

addAnno :: Annotation -> State Sign ()
addAnno (Annotation as apr _) = do
    addAnnoProp apr
    addAnnos as

addAnnos :: Annotations -> State Sign ()
addAnnos = mapM_ addAnno

addAnnoList :: (a -> State Sign ()) -> AnnotatedList a -> State Sign ()
addAnnoList f al = do
    addAnnos $ concatMap fst al
    mapM_ (f . snd) al

{- | Adds possible ListFrameBits to the Signature by calling
bottom level functions -}
extLFB :: Maybe Relation -> ListFrameBit -> State Sign ()
extLFB r lfb = case lfb of
    AnnotationBit ab ->
      unless (r `elem` [Just (DRRelation ADomain), Just (DRRelation ARange)])
        $ addAnnoList addAnnoProp ab
    ExpressionBit al -> addAnnoList addDescription al
    ObjectBit anob -> addAnnoList addObjPropExpr anob
    DataBit dlst -> addAnnoList addDataPropExpr dlst
    IndividualSameOrDifferent anind -> addAnnoList addIndividual anind
    ObjectCharacteristics al -> addAnnos $ concatMap fst al
    DataPropRange dr -> addAnnoList addDataRange dr
    IndividualFacts fct -> addAnnoList addFact fct

{- | Adds AnnotationFrameBits to the Signature
by calling the corresponding bottom level functions -}
extAFB :: AnnFrameBit -> State Sign ()
extAFB afb = case afb of
    AnnotationFrameBit _ -> return ()
    DataFunctional -> return ()
    DatatypeBit dr -> addDataRange dr
    ClassDisjointUnion cls -> mapM_ addDescription cls
    ClassHasKey obe dpe -> do
      mapM_ addObjPropExpr obe
      mapM_ addDataPropExpr dpe
    ObjectSubPropertyChain ope -> mapM_ addObjPropExpr ope

{- | Calls the completion of Signature based on
case separation of ListFrameBit and AnnotationFrameBit -}
extFB :: Extended -> FrameBit -> State Sign ()
extFB ext fb = case fb of
  ListFrameBit rel lfb -> do
    addExt ext
    extLFB rel lfb
  AnnFrameBit an anf -> do
    addAnnos an
    extAFB anf
    case anf of
        AnnotationFrameBit Assertion -> case ext of
            Misc _ -> return ()
            _ -> addExt ext
        _ -> addExt ext

extFrame :: Frame -> State Sign ()
extFrame (Frame ex fblist) = mapM_ (extFB ex) fblist

addExt :: Extended -> State Sign ()
addExt ext = case ext of
    SimpleEntity e -> addEntity e
    ObjectEntity op -> addObjPropExpr op
    ClassEntity ce -> addDescription ce
    Misc ans -> addAnnos ans

{- | Top level function: takes the OntologyDocument and completes
the signature by calling completeSignForFrame -}
extractSign :: OntologyDocument -> State Sign ()
extractSign od =
  mapM_ extFrame $ ontFrames $ ontology od

toDecl :: Sign -> [Frame]
toDecl s =
    let cls = map (Entity Class) $ Set.toList (concepts s)
        dt = map (Entity Datatype) $ Set.toList (datatypes s)
        op = map (Entity ObjectProperty) $ Set.toList (objectProperties s)
        dp = map (Entity DataProperty) $ Set.toList (dataProperties s)
        i = map (Entity NamedIndividual) $ Set.toList (individuals s)
        ans = map (Entity AnnotationProperty) $ Set.toList (annotationRoles s)
    in map (\ c -> Frame (SimpleEntity c)
        [AnnFrameBit [] $ AnnotationFrameBit Declaration])
            (cls ++ dt ++ op ++ dp ++ i ++ ans)

signToFrames :: [Frame] -> [Frame]
signToFrames f =
    let s = mapM_ extFrame f
    in toDecl $ execState s emptySign
