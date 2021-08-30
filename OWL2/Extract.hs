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

fromIndividualArg :: AS.IndividualArg -> State Sign ()
fromIndividualArg i = case i of
  AS.IArg i -> fromIndividual i
  _ -> return ()

fromDataArg :: AS.DataArg -> State Sign ()
fromDataArg d = case d of
  AS.DArg l -> fromLiteral l
  _ -> return ()

fromDLAtom :: AS.Atom -> State Sign ()
fromDLAtom atom = case atom of
  AS.ClassAtom c iArg -> do
    fromDescription c
    fromIndividualArg iArg
  AS.DataRangeAtom r d -> do
    fromDataRange r
    fromDataArg d
  AS.ObjectPropertyAtom o i1 i2 -> do
    fromObjPropExpr o
    fromIndividualArg i1
    fromIndividualArg i2
  AS.DataPropertyAtom p i d -> do
    fromDataPropExpr p
    fromIndividualArg i
    fromDataArg d
  AS.BuiltInAtom i args -> do
    -- TODO? what about iri (i)?
    mapM_ fromDataArg args
  AS.SameIndividualAtom i1 i2 -> do
    fromIndividualArg i1
    fromIndividualArg i2
  AS.DifferentIndividualsAtom i1 i2 -> do
    fromIndividualArg i1
    fromIndividualArg i2
  _ -> return () -- unknown atoms are eliminated in static analysis

fromDGAtom :: AS.DGAtom -> State Sign ()
fromDGAtom a = case a of
  AS.DGClassAtom c i -> do
    fromDescription c
    fromIndividualArg i
  AS.DGObjectPropertyAtom o i1 i2 -> do
    fromObjPropExpr o
    fromIndividualArg i1
    fromIndividualArg i2

fromAxiom :: AS.Axiom -> State Sign ()
fromAxiom a = case a of
    AS.Declaration anns e -> addEntity e
    
    AS.ClassAxiom cax -> case cax of
        AS.SubClassOf anns sub sup -> do
          fromAnnos anns
          fromDescription sub
          fromDescription sup
          
        AS.EquivalentClasses anns clExprs -> do
          fromAnnos anns
          mapM_ fromDescription clExprs
          
        AS.DisjointClasses anns clExprs -> do
          fromAnnos anns
          mapM_ fromDescription clExprs
          
        AS.DisjointUnion anns clIri clExprs -> do
          fromAnnos anns
          fromDescription (AS.Expression clIri)
          mapM_ fromDescription clExprs

    AS.ObjectPropertyAxiom opax -> case opax of
        AS.SubObjectPropertyOf anns subObjProp supObjProp -> do
          fromAnnos anns
          fromObjPropExpr supObjProp
          case subObjProp of
            AS.SubObjPropExpr_obj op -> fromObjPropExpr op
            AS.SubObjPropExpr_exprchain ops -> mapM_ fromObjPropExpr ops
             
        AS.EquivalentObjectProperties anns ops -> do
          fromAnnos anns 
          mapM_ fromObjPropExpr ops

        AS.DisjointObjectProperties anns ops -> do
          fromAnnos anns
          mapM_ fromObjPropExpr ops
          
        AS.InverseObjectProperties anns op1 op2 -> do
          fromAnnos anns
          mapM_ fromObjPropExpr [op1, op2]

        AS.ObjectPropertyDomain anns op des -> do
          fromAnnos anns
          fromObjPropExpr op
          fromDescription des

        AS.ObjectPropertyRange anns op des -> do
          fromAnnos anns
          fromObjPropExpr op
          fromDescription des

        AS.FunctionalObjectProperty anns op -> do
          fromAnnos anns
          fromObjPropExpr op
           
        AS.InverseFunctionalObjectProperty anns op -> do
          fromAnnos anns
          fromObjPropExpr op
           
        AS.ReflexiveObjectProperty anns op -> do
          fromAnnos anns
          fromObjPropExpr op
          
        AS.IrreflexiveObjectProperty anns op -> do
          fromAnnos anns
          fromObjPropExpr op
          
        AS.SymmetricObjectProperty anns op -> do
          fromAnnos anns
          fromObjPropExpr op

        AS.AsymmetricObjectProperty anns op -> do
          fromAnnos anns
          fromObjPropExpr op
          
        AS.TransitiveObjectProperty anns op -> do
          fromAnnos anns
          fromObjPropExpr op
          
    AS.DataPropertyAxiom a -> case a of
        AS.SubDataPropertyOf anns dpSub dpSup -> do
          fromAnnos anns
          mapM_ fromDataPropExpr [dpSub, dpSup]
          
        AS.EquivalentDataProperties anns dps -> do
          fromAnnos anns
          mapM_ fromDataPropExpr dps

        AS.DisjointDataProperties anns dps -> do
          fromAnnos anns
          mapM_ fromDataPropExpr dps

        AS.DataPropertyDomain anns dp des -> do
          fromAnnos anns
          fromDataPropExpr dp
          fromDescription des

        AS.DataPropertyRange anns dp r -> do
          fromAnnos anns
          fromDataPropExpr dp
          fromDataRange r

        AS.FunctionalDataProperty anns dp -> do
          fromAnnos anns
          fromDataPropExpr dp
           
    AS.DatatypeDefinition anns dt dr -> do
      fromAnnos anns
      fromDType dt
      fromDataRange dr

    AS.HasKey anns des ops dps -> do
      fromAnnos anns
      fromDescription des
      mapM_ fromObjPropExpr ops
      mapM_ fromDataPropExpr dps
       
    AS.Assertion a -> case a of
        AS.SameIndividual anns inds -> do
          fromAnnos anns
          mapM_ fromIndividual inds
          
        AS.DifferentIndividuals anns inds -> do 
          fromAnnos anns
          mapM_ fromIndividual inds
          
        AS.ClassAssertion anns c i -> do
          fromAnnos anns
          fromDescription c
          fromIndividual i
        AS.ObjectPropertyAssertion anns o s t -> do
          fromAnnos anns
          fromObjPropExpr o
          fromIndividual s
          fromIndividual t
        AS.NegativeObjectPropertyAssertion anns o s t -> do
          fromAnnos anns
          fromObjPropExpr o
          fromIndividual s
          fromIndividual t
        AS.DataPropertyAssertion anns d s t -> do
          fromAnnos anns
          fromDataPropExpr d
          fromIndividual s
          fromLiteral t
        AS.NegativeDataPropertyAssertion anns d s t -> do
          fromAnnos anns
          fromDataPropExpr d
          fromIndividual s
          fromLiteral t
          
    AS.AnnotationAxiom a -> case a of
        AS.AnnotationAssertion anns p s v -> do
          fromAnnos anns
          fromAnnoProp p
          -- TODO: What about subject?
          case v of
            AS.AnnValLit l -> fromLiteral l
            -- TODO: What about AnnValue?
        AS.SubAnnotationPropertyOf anns sub sup -> do
          fromAnnos anns
          fromAnnoProp sub
          fromAnnoProp sup
        AS.AnnotationPropertyDomain anns p d -> do
          -- TODO: What about Domain?
          fromAnnos anns
          fromAnnoProp p
        AS.AnnotationPropertyRange anns p r -> do
          -- TODO: What about Range?
          fromAnnos anns
          fromAnnoProp p
    AS.Rule r -> case r of
      AS.DLSafeRule anns b h -> do
        fromAnnos anns
        mapM_ fromDLAtom b
        mapM_ fromDLAtom h
      AS.DGRule anns b h -> do
        fromAnnos anns
        mapM_ fromDGAtom b
        mapM_ fromDGAtom h
    AS.DGAxiom anns _ nodes edges classes -> do
      mapM_ (\(AS.DGNodeAssertion c _) -> fromDescription (AS.Expression c)) nodes
      mapM_ (\(AS.DGEdgeAssertion o _ _) -> fromObjPropExpr (AS.ObjectProp o)) edges
      mapM_ (fromDescription . AS.Expression) classes

{- | Top level function: takes the OntologyDocument and completes
the signature by calling completeSignForFrame -}
extractSign :: AS.OntologyDocument -> State Sign ()
extractSign = mapM_ fromAxiom . AS.axioms . AS.ontology

toDecl :: Sign -> [AS.Axiom]
toDecl s =
    let cls = map (AS.mkEntity AS.Class) $ Set.toList (concepts s)
        dt = map (AS.mkEntity AS.Datatype) $ Set.toList (datatypes s)
        op = map (AS.mkEntity AS.ObjectProperty) $ Set.toList (objectProperties s)
        dp = map (AS.mkEntity AS.DataProperty) $ Set.toList (dataProperties s)
        i = map (AS.mkEntity AS.NamedIndividual) $ Set.toList (individuals s)
        ans = map (AS.mkEntity AS.AnnotationProperty) $ Set.toList (annotationRoles s)
    in map (AS.Declaration []) (cls ++ dt ++ op ++ dp ++ i ++ ans)

-- signToFrames :: [Frame] -> [Frame]
-- signToFrames f = let s = mapM_ fromFrame f in toDecl $ execState s emptySign
-- TODO: commented out in 1993
signToFrames :: [Frame] -> [Frame]
signToFrames = id
