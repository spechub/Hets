{- |
Module      :  $Header$
Description :  Comorphism from OWL 1.1 to DL
Copyright   :  (c) Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (via Logic.Logic)

a not yet implemented comorphism
-}

module Comorphisms.OWL2DL where

import Logic.Logic
import Logic.Comorphism

--OWL = domain
import OWL.Logic_OWL11
import OWL.AS
import OWL.Sign as OWL

--DL = codomain
import DL.Logic_DL
import DL.AS
import DL.Sign as DL

import Common.AS_Annotation
import Common.DocUtils
import Common.Id
import Common.ProofTree
import Common.Result

import qualified Data.Set as Set

data OWL2DL = OWL2DL deriving Show

instance Language OWL2DL

instance Comorphism
    OWL2DL     -- comorphism
    OWL11           -- lid domain
    ()              -- sublogics domain
    OntologyFile    -- Basic spec domain
    Sentence        -- sentence domain
    ()              -- symbol items domain
    ()              -- symbol map items domain
    OWL.Sign        -- signature domain
    OWL11_Morphism  -- morphism domain
    ()              -- symbol domain
    ()              -- rawsymbol domain
    ProofTree   -- proof tree codomain
    DL         -- lid codomain
    ()                     -- Sublogics
    DLBasic                -- basic_spec
    DLBasicItem            -- sentence
    ()                     -- symb_items
    ()                     -- symb_map_items
    DL.Sign                -- sign
    DLMorphism             -- morphism
    DLSymbol               -- symbol
    RawDLSymbol            -- raw_symbol
    ()                     -- proof_tree
    where
    sourceLogic OWL2DL    = OWL11
    sourceSublogic OWL2DL = ()
    targetLogic OWL2DL    = DL
    mapSublogic OWL2DL _  = Just ()
    map_theory OWL2DL = mapTheory
    map_morphism = mapDefaultMorphism

qNameToId :: QName -> Id
qNameToId = stringToId . localPart

mapTheory :: (OWL.Sign, [Named Sentence])
          -> Result (DL.Sign, [Named DLBasicItem])
mapTheory (osign, sens) = do
  let
    cs = Set.map qNameToId $ concepts osign
    ps = Set.map qNameToId $ datatypes osign
    ds = Set.map (QualDataProp . qNameToId) $ dataValuedRoles osign
    os = Set.map (QualObjProp . qNameToId) $ indValuedRoles osign
    is = Set.map (flip QualIndiv [] . qNameToId) $ OWL.individuals osign
  ns <- mapM (mapNamedM mapSenM) sens
  return (emptyDLSig
    { classes = Set.union cs $ classes emptyDLSig
    , pData = Set.union ps $ pData emptyDLSig
    , dataProps = ds
    , objectProps = Set.union os $ objectProps emptyDLSig
    , DL.individuals = is}, ns)

getAxiom :: Sentence -> Axiom
getAxiom s = case s of
  OWLAxiom a -> a
  OWLFact a -> a

toDLJunction :: JunctionType -> DLConcept -> DLConcept -> Range -> DLConcept
toDLJunction ty = case ty of
  UnionOf -> DLOr
  IntersectionOf -> DLAnd

toConcept :: Description -> Result DLConcept
toConcept des = let err = fail $ "OWL2DL.toConcept " ++ showDoc des "" in
  case des of
  OWLClass curi -> return $ DLClassId (qNameToId curi) nullRange
  ObjectJunction ty ds | not $ null ds -> do
    cs <- mapM toConcept ds
    return $ foldr1 (\ c1 c2 -> toDLJunction ty c1 c2 nullRange) cs
  ObjectComplementOf d -> do
    c <- toConcept d
    return $ DLNot c nullRange
  ObjectOneOf is -> return $ DLOneOf (map qNameToId is) nullRange
  _ -> err
{-
  ObjectAllValuesFrom ope d
  ObjectSomeValuesFrom ope d
  ObjectExistsSelf ope
  ObjectHasValue ope i
  ObjectMinCardinality c ope md
  ObjectMaxCardinality c ope md
  ObjectExactCardinality c ope md
  DataAllValuesFrom dpe dpes dr
  DataSomeValuesFrom dpe dpes dr
  DataHasValue dpe con
  DataMinCardinality c dpe mdr
  DataMaxCardinality c dpe mdr
  DataExactCardinality c dpe mdr
-}

mapSenM :: Sentence -> Result DLBasicItem
mapSenM sen = let err = fail $ "OWL2DL.mapSenM " ++ showDoc sen "" in
  case getAxiom sen of
  SubClassOf _as sub super -> case sub of
    OWLClass curi -> do
        c <- toConcept super
        return $ DLClass (qNameToId curi)
          [DLSubClassof [c] nullRange] Nothing nullRange
    _ -> err
  EquivalentClasses _as (cl : cs) -> case cl of
    OWLClass curi -> do
        es <- mapM toConcept cs
        return $ DLClass (qNameToId curi)
          [DLEquivalentTo es nullRange] Nothing nullRange
    _ -> err
  DisjointClasses _as (cl : cs) -> case cl of
    OWLClass curi -> do
        es <- mapM toConcept cs
        return $ DLClass (qNameToId curi)
          [DLDisjointWith es nullRange] Nothing nullRange
    _ -> err
  _ -> err
{-
  DisjointUnion _as OwlClassURI ds ->
  SubObjectPropertyOf _as subOpe ope ->
  EquivalentObjectProperties _as opes ->
  DisjointObjectProperties _as opes ->
  ObjectPropertyDomain _as ope d ->
  ObjectPropertyRange _as ope d ->
  InverseObjectProperties _as ope ope ->
  FunctionalObjectProperty _as ope ->
  InverseFunctionalObjectProperty _as ope ->
  ReflexiveObjectProperty _as ope ->
  IrreflexiveObjectProperty _as ope ->
  SymmetricObjectProperty _as ope ->
  AntisymmetricObjectProperty _as ope ->
  TransitiveObjectProperty _as ope ->
           -- DataPropertyAxiom
  SubDataPropertyOf _as dpe dpe ->
  EquivalentDataProperties _as dpes ->
  DisjointDataProperties _as dpes ->
  DataPropertyDomain _as dpe d ->
  DataPropertyRange _as dpe dr ->
  FunctionalDataProperty _as dpe ->
           -- Fact
  SameIndividual _as is ->
  DifferentIndividuals _as is ->
  ClassAssertion _as i d ->
  ObjectPropertyAssertion _as ope si ti ->
  NegativeObjectPropertyAssertion _as ope si ti ->
  DataPropertyAssertion _as dpe si tv ->
  NegativeDataPropertyAssertion _as dpe si tv ->
  Declaration _as e ->
  EntityAnno ea ->
-}
