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

import qualified Data.Set as Set

data NumberRestrictions = None | Unqualified | Qualified
    deriving (Show, Eq, Ord)

owlDatatypes :: Set.Set Datatype
owlDatatypes = Set.fromList predefIRIs

data OWLSub = OWLSub
    { numberRestrictions :: NumberRestrictions
    , nominals :: Bool
    , inverseRoles :: Bool
    , roleTransitivity :: Bool
    , roleHierarchy :: Bool
    , complexRoleInclusions :: Bool
    , addFeatures :: Bool
    , datatype :: Set.Set Datatype
    } deriving (Show, Eq, Ord)

-- | sROIQ(D)
sl_top :: OWLSub
sl_top = OWLSub
    { numberRestrictions = Qualified
    , nominals = True
    , inverseRoles = True
    , roleTransitivity = True
    , roleHierarchy = True
    , complexRoleInclusions = True
    , addFeatures = True
    , datatype = owlDatatypes
    }

-- ALC
sl_bottom :: OWLSub
sl_bottom = OWLSub
    { numberRestrictions = None
    , nominals = False
    , inverseRoles = False
    , roleTransitivity = False
    , roleHierarchy = False
    , complexRoleInclusions = False
    , addFeatures = False
    , datatype = Set.empty
    }


sl_max :: OWLSub -> OWLSub -> OWLSub
sl_max sl1 sl2 = OWLSub
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
sl_name :: OWLSub -> String
sl_name sl =
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
           "-D"
           ++ (if Set.null ds then "" else
                 "|"
                 ++ (if ds == owlDatatypes then "-" else
                         intercalate "|" $ map printDatatype $ Set.toList ds)
                 ++ "|")

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
slDatatype dt = sl_bottom {datatype = if isDatatypeKey dt then
    Set.singleton $ stripReservedPrefix dt else Set.singleton dt}

slDataProp :: DataPropertyExpression -> OWLSub
slDataProp = slDatatype

slObjProp :: ObjectPropertyExpression -> OWLSub
slObjProp o = case o of
    ObjectProp _ -> sl_bottom
    ObjectInverseOf _ -> requireInverseRoles sl_bottom

slEntity :: Entity -> OWLSub
slEntity (Entity et iri) = case et of
    Datatype -> slDatatype iri
    _ -> sl_bottom

slDataRange :: DataRange -> OWLSub
slDataRange rn = case rn of
    DataType ur _ -> slDatatype ur
    DataComplementOf c -> slDataRange c
    DataOneOf _ -> requireNominals sl_bottom
    DataJunction _ drl -> foldl sl_max sl_bottom $ map slDataRange drl

slClassExpression :: ClassExpression -> OWLSub
slClassExpression des = case des of
    Expression _ -> sl_bottom
    ObjectJunction _ dec -> foldl sl_max sl_bottom $ map slClassExpression dec
    ObjectComplementOf dec -> slClassExpression dec
    ObjectOneOf _ -> requireNominals sl_bottom
    ObjectValuesFrom _ o d -> sl_max (slObjProp o) (slClassExpression d)
    ObjectHasSelf o -> requireAddFeatures $ slObjProp o
    ObjectHasValue o _ -> slObjProp o
    ObjectCardinality c -> slObjCard c
    DataValuesFrom _ d dr -> sl_max (slDataRange dr) (slDataProp d)
    DataHasValue d _ -> slDataProp d
    DataCardinality c -> slDataCard c

slDataCard :: Cardinality DataPropertyExpression DataRange -> OWLSub
slDataCard (Cardinality _ _ dp x) = requireNumberRestrictions $ case x of
    Nothing -> slDataProp dp
    Just y -> sl_max (slDataProp dp) (slDataRange y)

slObjCard :: Cardinality ObjectPropertyExpression ClassExpression -> OWLSub
slObjCard (Cardinality _ _ op x) = requireNumberRestrictions $ case x of
    Nothing -> slObjProp op
    Just y -> sl_max (slObjProp op) (slClassExpression y)

slLFB :: Maybe Relation -> ListFrameBit -> OWLSub
slLFB mr lfb = case lfb of
    ExpressionBit anl -> foldl sl_max sl_bottom $ map (slClassExpression . snd) anl
    ObjectBit anl -> sl_max (case fromMaybe (error "relation needed") mr of
        EDRelation Disjoint -> requireAddFeatures sl_bottom
        _ -> sl_bottom) $ foldl sl_max sl_bottom $ map (slObjProp . snd) anl
    DataBit anl -> sl_max (case fromMaybe (error "relation needed") mr of
        EDRelation Disjoint -> requireAddFeatures sl_bottom
        _ -> sl_bottom) $ foldl sl_max sl_bottom $ map (slDataProp . snd) anl
    IndividualSameOrDifferent _ -> requireNominals sl_bottom
    ObjectCharacteristics anl -> foldl sl_max sl_bottom
        $ map (\ c -> case c of
              Transitive -> requireRoleTransitivity sl_bottom
              Reflexive -> requireAddFeatures sl_bottom
              Irreflexive -> requireAddFeatures sl_bottom
              Asymmetric -> requireAddFeatures sl_bottom
              _ -> sl_bottom) $ map snd anl
    DataPropRange anl -> foldl sl_max sl_bottom $ map (slDataRange . snd) anl
    _ -> sl_bottom

slAFB :: AnnFrameBit -> OWLSub
slAFB afb = case afb of
    DatatypeBit dr -> slDataRange dr
    ClassDisjointUnion cel -> foldl sl_max sl_bottom $ map slClassExpression cel
    ClassHasKey opl dpl -> sl_max (foldl sl_max sl_bottom $ map slObjProp opl)
            (foldl sl_max sl_bottom $ map slDataProp dpl)
    ObjectSubPropertyChain opl -> requireComplexRoleInclusions
        $ requireRoleHierarchy $ foldl sl_max sl_bottom $ map slObjProp opl
    _ -> sl_bottom

slFB :: FrameBit -> OWLSub
slFB fb = case fb of
    AnnFrameBit _ afb -> slAFB afb
    ListFrameBit mr lfb -> sl_max (slLFB mr lfb) $ case mr of
        Nothing -> sl_bottom
        Just r -> case r of
            SubPropertyOf -> requireRoleHierarchy sl_bottom
            InverseOf -> requireInverseRoles sl_bottom
            _ -> sl_bottom -- maybe addFeatures ??

slAxiom :: Axiom -> OWLSub
slAxiom (PlainAxiom ext fb) = case ext of
    Misc _ -> slFB fb
    ClassEntity ce -> sl_max (slFB fb) (slClassExpression ce)
    ObjectEntity o -> sl_max (slFB fb) (slObjProp o)
    SimpleEntity e@(Entity ty ent) -> case ty of
        DataProperty -> sl_max (slFB fb) (slDataProp ent)
        _ -> sl_max (slEntity e) (slFB fb)

slFrame :: Frame -> OWLSub
slFrame = foldl sl_max sl_bottom . map slAxiom . getAxioms

sl_o_doc :: OntologyDocument -> OWLSub
sl_o_doc = foldl sl_max sl_bottom . map slFrame . ontFrames . ontology

sl_sig :: Sign -> OWLSub
sl_sig sig = let dts = Set.toList $ datatypes sig in
    if Set.size (dataProperties sig) == 0 && null dts
    then sl_bottom else foldl sl_max sl_bottom $ map slDatatype dts

sl_mor :: OWLMorphism -> OWLSub
sl_mor mor = sl_max (sl_sig $ osource mor) $ sl_sig $ otarget mor

-- projections along sublogics
pr_mor :: OWLSub -> OWLMorphism -> OWLMorphism
pr_mor s a = a
    { osource = pr_sig s $ osource a
    , otarget = pr_sig s $ otarget a }

pr_sig :: OWLSub -> Sign -> Sign
pr_sig s a = if datatype s == Set.empty
    then a {datatypes = Set.empty, dataProperties = Set.empty}
    else a

pr_o_doc :: OWLSub -> OntologyDocument -> OntologyDocument
pr_o_doc s a =
    let o = (ontology a) {ontFrames = filter ((s >=) . slFrame) $ ontFrames $
            ontology a }
    in a {ontology = o}
