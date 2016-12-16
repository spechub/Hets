{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  $Header$
Copyright   :  (c) Dominik Luecke, Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Complexity analysis of OWL2

-}

module OWL2.Sublogic where

import OWL2.AS
import OWL2.MS
import OWL2.Sign
import OWL2.Morphism

import Data.List
import Data.Maybe

import Data.Data
import qualified Data.Set as Set

data NumberRestrictions = None | Unqualified | Qualified
    deriving (Show, Eq, Ord, Typeable, Data)

owlDatatypes :: Set.Set Datatype
owlDatatypes = predefIRIs

data OWLSub = OWLSub
    { numberRestrictions :: NumberRestrictions
    , nominals :: Bool
    , inverseRoles :: Bool
    , roleTransitivity :: Bool
    , roleHierarchy :: Bool
    , complexRoleInclusions :: Bool
    , addFeatures :: Bool
    , datatype :: Set.Set Datatype
    } deriving (Show, Eq, Ord, Typeable, Data)

allSublogics :: [[OWLSub]]
allSublogics = let
  t = True
  b = slBottom
  in
  [ [ b { numberRestrictions = Unqualified }
    , b { numberRestrictions = Qualified } ]
  , [b { nominals = t } ]
  , [b { inverseRoles = t } ]
  , [b { roleTransitivity = t } ]
  , [b { roleHierarchy = t } ]
  , [b { complexRoleInclusions = t } ]
  , [b { addFeatures = t } ]
  , map (\ d -> b { datatype = Set.singleton d }) $ Set.toList owlDatatypes ]

-- | sROIQ(D)
slTop :: OWLSub
slTop = OWLSub
    { numberRestrictions = Qualified
    , nominals = True
    , inverseRoles = True
    , roleTransitivity = True
    , roleHierarchy = True
    , complexRoleInclusions = True
    , addFeatures = True
    , datatype = owlDatatypes
    }

-- | ALC
slBottom :: OWLSub
slBottom = OWLSub
    { numberRestrictions = None
    , nominals = False
    , inverseRoles = False
    , roleTransitivity = False
    , roleHierarchy = False
    , complexRoleInclusions = False
    , addFeatures = False
    , datatype = Set.empty
    }


slMax :: OWLSub -> OWLSub -> OWLSub
slMax sl1 sl2 = OWLSub
    { numberRestrictions = max (numberRestrictions sl1) (numberRestrictions sl2)
    , nominals = max (nominals sl1) (nominals sl2)
    , inverseRoles = max (inverseRoles sl1) (inverseRoles sl2)
    , roleTransitivity = max (roleTransitivity sl1) (roleTransitivity sl2)
    , roleHierarchy = max (roleHierarchy sl1) (roleHierarchy sl2)
    , complexRoleInclusions = max (complexRoleInclusions sl1)
            (complexRoleInclusions sl2)
    , addFeatures = max (addFeatures sl1) (addFeatures sl2)
    , datatype = Set.union (datatype sl1) (datatype sl2)
    }

-- | Naming for Description Logics
slName :: OWLSub -> String
slName sl =
    (if complexRoleInclusions sl || addFeatures sl
       then (if addFeatures sl then "s" else "") ++ "R"
       else (if roleTransitivity sl then "S" else "ALC")
            ++ if roleHierarchy sl then "H" else "")
    ++ (if nominals sl then "O" else "")
    ++ (if inverseRoles sl then "I" else "")
    ++ (case numberRestrictions sl of
        Qualified -> "Q"
        Unqualified -> "N"
        None -> "")
    ++ let ds = datatype sl in if Set.null ds then "" else
           "-D|" ++ (if ds == owlDatatypes then "-|" else
                intercalate "|" (map printDatatype $ Set.toList ds) ++ "|")

requireQualNumberRestrictions :: OWLSub -> OWLSub
requireQualNumberRestrictions sl = sl {numberRestrictions = Qualified}

requireNumberRestrictions :: OWLSub -> OWLSub
requireNumberRestrictions sl = let nr = numberRestrictions sl in
    sl {numberRestrictions = if nr /= Qualified then Unqualified else nr}

requireRoleTransitivity :: OWLSub -> OWLSub
requireRoleTransitivity sl = sl {roleTransitivity = True}

requireRoleHierarchy :: OWLSub -> OWLSub
requireRoleHierarchy sl = sl {roleHierarchy = True}

requireComplexRoleInclusions :: OWLSub -> OWLSub
requireComplexRoleInclusions sl = (requireRoleHierarchy
    $ requireRoleTransitivity sl) {complexRoleInclusions = True}

requireAddFeatures :: OWLSub -> OWLSub
requireAddFeatures sl = (requireComplexRoleInclusions sl) {addFeatures = True}

requireNominals :: OWLSub -> OWLSub
requireNominals sl = sl {nominals = True}

requireInverseRoles :: OWLSub -> OWLSub
requireInverseRoles sl = sl {inverseRoles = True}

slDatatype :: Datatype -> OWLSub
slDatatype dt = slBottom {datatype = if isDatatypeKey dt then
    Set.singleton $ setDatatypePrefix dt else Set.empty}

slObjProp :: ObjectPropertyExpression -> OWLSub
slObjProp o = case o of
    ObjectProp _ -> slBottom
    ObjectInverseOf _ -> requireInverseRoles slBottom

slEntity :: Entity -> OWLSub
slEntity (Entity _ et iri) = case et of
    Datatype -> slDatatype iri
    _ -> slBottom

slDataRange :: DataRange -> OWLSub
slDataRange rn = case rn of
    DataType ur _ -> slDatatype ur
    DataComplementOf c -> slDataRange c
    DataOneOf _ -> requireNominals slBottom
    DataJunction _ drl -> foldl slMax slBottom $ map slDataRange drl

slClassExpression :: ClassExpression -> OWLSub
slClassExpression des = case des of
    ObjectJunction _ dec -> foldl slMax slBottom $ map slClassExpression dec
    ObjectComplementOf dec -> slClassExpression dec
    ObjectOneOf _ -> requireNominals slBottom
    ObjectValuesFrom _ o d -> slMax (slObjProp o) (slClassExpression d)
    ObjectHasSelf o -> requireAddFeatures $ slObjProp o
    ObjectHasValue o _ -> slObjProp o
    ObjectCardinality c -> slObjCard c
    DataValuesFrom _ _ dr -> slDataRange dr
    DataCardinality c -> slDataCard c
    _ -> slBottom

slDataCard :: Cardinality DataPropertyExpression DataRange -> OWLSub
slDataCard (Cardinality _ _ _ x) = requireNumberRestrictions $ case x of
    Nothing -> slBottom
    Just y -> slDataRange y

slObjCard :: Cardinality ObjectPropertyExpression ClassExpression -> OWLSub
slObjCard (Cardinality _ _ op x) = requireNumberRestrictions $ case x of
    Nothing -> slObjProp op
    Just y -> slMax (slObjProp op) (slClassExpression y)

slLFB :: Maybe Relation -> ListFrameBit -> OWLSub
slLFB mr lfb = case lfb of
    ExpressionBit anl -> foldl slMax slBottom
        $ map (slClassExpression . snd) anl
    ObjectBit anl -> slMax (case fromMaybe (error "relation needed") mr of
        EDRelation Disjoint -> requireAddFeatures slBottom
        _ -> slBottom) $ foldl slMax slBottom $ map (slObjProp . snd) anl
    DataBit _ -> case fromMaybe (error "relation needed") mr of
        EDRelation Disjoint -> requireAddFeatures slBottom
        _ -> slBottom
    IndividualSameOrDifferent _ -> requireNominals slBottom
    ObjectCharacteristics anl -> foldl slMax slBottom
        $ map ((\ c -> case c of
              Transitive -> requireRoleTransitivity slBottom
              Reflexive -> requireAddFeatures slBottom
              Irreflexive -> requireAddFeatures slBottom
              Asymmetric -> requireAddFeatures slBottom
              _ -> slBottom) . snd) anl
    DataPropRange anl -> foldl slMax slBottom $ map (slDataRange . snd) anl
    _ -> slBottom

slAFB :: AnnFrameBit -> OWLSub
slAFB afb = case afb of
    DatatypeBit dr -> slDataRange dr
    ClassDisjointUnion cel -> foldl slMax slBottom $ map slClassExpression cel
    ClassHasKey opl _ -> foldl slMax slBottom $ map slObjProp opl
    ObjectSubPropertyChain opl -> requireComplexRoleInclusions
        $ requireRoleHierarchy $ foldl slMax slBottom $ map slObjProp opl
    _ -> slBottom

slFB :: FrameBit -> OWLSub
slFB fb = case fb of
    AnnFrameBit _ afb -> slAFB afb
    ListFrameBit mr lfb -> slMax (slLFB mr lfb) $ case mr of
        Nothing -> slBottom
        Just r -> case r of
            SubPropertyOf -> requireRoleHierarchy slBottom
            InverseOf -> requireInverseRoles slBottom
            _ -> slBottom -- maybe addFeatures ??

slAxiom :: Axiom -> OWLSub
slAxiom (PlainAxiom ext fb) = case ext of
    Misc _ -> slFB fb
    ClassEntity ce -> slMax (slFB fb) (slClassExpression ce)
    ObjectEntity o -> slMax (slFB fb) (slObjProp o)
    SimpleEntity e -> slMax (slEntity e) (slFB fb)

slFrame :: Frame -> OWLSub
slFrame = foldl slMax slBottom . map slAxiom . getAxioms

slODoc :: OntologyDocument -> OWLSub
slODoc = foldl slMax slBottom . map slFrame . ontFrames . ontology

slSig :: Sign -> OWLSub
slSig sig = let dts = Set.toList $ datatypes sig in
    if Set.size (dataProperties sig) == 0 && null dts
    then slBottom else foldl slMax slBottom $ map slDatatype dts

slMor :: OWLMorphism -> OWLSub
slMor mor = slMax (slSig $ osource mor) $ slSig $ otarget mor

-- projections along sublogics
prMor :: OWLSub -> OWLMorphism -> OWLMorphism
prMor s a = a
    { osource = prSig s $ osource a
    , otarget = prSig s $ otarget a }

prSig :: OWLSub -> Sign -> Sign
prSig s a = if datatype s == Set.empty
    then a {datatypes = Set.empty, dataProperties = Set.empty}
    else a

prODoc :: OWLSub -> OntologyDocument -> OntologyDocument
prODoc s a =
    let o = (ontology a) {ontFrames = filter ((s >=) . slFrame) $ ontFrames $
            ontology a }
    in a {ontology = o}
