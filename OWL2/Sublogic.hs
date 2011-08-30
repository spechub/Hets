{- |
Module      :  $Header$
Copyright   :  (c) Dominik Luecke, Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Here is the place where the class Logic is instantiated for OWL2 DL.

-}

module OWL2.Sublogic
    ( OWLSub (..)
    , NumberRestrictions (..)
    , OWLDatatypes (..)
    , sl_top
    , sl_bottom
    , sl_max
    , sl_name
    , slFrame
    , slAxiom
    , sl_o_doc
    , sl_sig
    , sl_mor
    , pr_o_doc
    , pr_sig
    , pr_mor
    , printXSDName
    ) where

import OWL2.AS
import OWL2.MS
import OWL2.Sign
import OWL2.Morphism

import Data.Char
import Data.List
import Data.Maybe

import qualified Data.Set as Set

data NumberRestrictions = None | Unqualified | Qualified
                        deriving (Show, Eq, Ord)

data OWLDatatypes = OWLDATA | OWLString |
                    OWLnormalizedString |
                    OWLBoolean | OWLDecimal | OWLFloat | OWLDouble |
                    OWLInteger | OWLnonNegativeInteger | OWLpositiveInteger |
                    OWLnonPositiveInteger | OWLnegativeInteger
               deriving (Show, Eq, Ord, Enum, Bounded)

owlDatatypes :: [OWLDatatypes]
owlDatatypes = [minBound .. maxBound]

printXSDName :: Show a => a -> String
printXSDName dt =
    drop 3 $ show dt

data OWLSub = OWLSub
            {
              numberRestrictions :: NumberRestrictions
            , nominals :: Bool
            , inverseRoles :: Bool
            , roleTransitivity :: Bool
            , roleHierarchy :: Bool
            , complexRoleInclusions :: Bool
            , addFeatures :: Bool
            , datatype :: Set.Set OWLDatatypes
            } deriving (Show, Eq, Ord)

-- | sROIQ(D)
sl_top :: OWLSub
sl_top = OWLSub
      {
        numberRestrictions = Qualified
      , nominals = True
      , inverseRoles = True
      , roleTransitivity = True
      , roleHierarchy = True
      , complexRoleInclusions = True
      , addFeatures = True
      , datatype = Set.fromList owlDatatypes
      }

-- ALC
sl_bottom :: OWLSub
sl_bottom = OWLSub
            {
              numberRestrictions = None
            , nominals = False
            , inverseRoles = False
            , roleTransitivity = False
            , roleHierarchy = False
            , complexRoleInclusions = False
            , addFeatures = False
            , datatype = Set.empty
            }


sl_max :: OWLSub -> OWLSub -> OWLSub
sl_max sl1 sl2 =
    OWLSub
    {
      numberRestrictions = max (numberRestrictions sl1)
                           (numberRestrictions sl2)
    , nominals = max (nominals sl1)
                 (nominals sl2)
    , inverseRoles = max (inverseRoles sl1)
                     (inverseRoles sl2)
    , roleTransitivity = max (roleTransitivity sl1)
                         (roleTransitivity sl2)
    , roleHierarchy = max (roleHierarchy sl1)
                      (roleHierarchy sl2)
    , complexRoleInclusions = max (complexRoleInclusions sl1)
                              (complexRoleInclusions sl2)
    , addFeatures = max (addFeatures sl1)
                    (addFeatures sl2)
    , datatype = Set.union (datatype sl1)
                 (datatype sl2)
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
           ++ (let ts = Set.filter (/= OWLDATA) ds
               in if Set.null ts then "" else
                 "|"
                 ++ (if ds == Set.fromList owlDatatypes then "-" else
                         intercalate "|" $ map printXSDName $ Set.toList ts)
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
requireComplexRoleInclusions sl =
    (requireRoleHierarchy $ requireRoleTransitivity sl)
        {complexRoleInclusions = True}

requireAddFeatures :: OWLSub -> OWLSub
requireAddFeatures sl = (requireComplexRoleInclusions sl) {addFeatures = True}

requireNominals :: OWLSub -> OWLSub
requireNominals sl = sl {nominals = True}

requireInverseRoles :: OWLSub -> OWLSub
requireInverseRoles sl = sl {inverseRoles = True}

requireDatatype :: OWLSub -> OWLSub
requireDatatype sl = sl {datatype = Set.union (datatype sl)
    $ Set.singleton OWLDATA}

sl_obj_prop :: ObjectPropertyExpression -> OWLSub
sl_obj_prop o = case o of
    ObjectProp _ -> sl_bottom
    ObjectInverseOf p -> requireInverseRoles $ sl_obj_prop p

sl_ent :: Entity -> OWLSub
sl_ent (Entity et _) = case et of
    Datatype -> requireDatatype sl_bottom
    _ -> sl_bottom

sl_data_uri :: QName -> OWLSub
sl_data_uri ur = sl_bottom
  { datatype = case namePrefix ur of
      "xsd" -> let
          l = map toLower $ localPart ur
          s = case l of
                '#' : r -> r
                _ -> l
          in Set.fromList $ OWLDATA
               : filter ((s ==) . map toLower . printXSDName) owlDatatypes
      _ -> Set.singleton OWLDATA }

sl_data_prop :: DataPropertyExpression -> OWLSub
sl_data_prop = sl_data_uri

sl_data_range :: DataRange -> OWLSub
sl_data_range rn = requireDatatype $ case rn of
    DataType ur _ -> sl_data_uri ur
    DataComplementOf c -> sl_data_range c
    DataOneOf _ -> requireNominals sl_bottom
    DataJunction _ drl -> foldl sl_max sl_bottom $ map sl_data_range drl

sl_desc :: ClassExpression -> OWLSub
sl_desc des = case des of
    Expression _ -> sl_bottom
    ObjectJunction _ dec -> foldl sl_max sl_bottom $ map sl_desc dec
    ObjectComplementOf dec -> sl_desc dec
    ObjectOneOf _ -> requireNominals sl_bottom
    ObjectValuesFrom _ o d -> sl_max (sl_obj_prop o) (sl_desc d)
    ObjectHasSelf o -> requireAddFeatures $ sl_obj_prop o
    ObjectHasValue o _ -> sl_obj_prop o
    ObjectCardinality c -> sl_card c
    DataValuesFrom _ d dr -> requireDatatype $
             sl_max (sl_data_range dr) (sl_data_prop d)
    DataHasValue d _ -> requireDatatype $ sl_data_prop d
    DataCardinality c -> requireDatatype $ sl_d_card c

sl_d_card :: Cardinality DataPropertyExpression DataRange -> OWLSub
sl_d_card (Cardinality _ _ dp x) = requireDatatype $ requireNumberRestrictions
    $ case x of
        Nothing -> sl_data_prop dp
        Just y -> sl_max (sl_data_prop dp) (sl_data_range y)

sl_card :: Cardinality ObjectPropertyExpression ClassExpression -> OWLSub
sl_card (Cardinality _ _ op x) = requireNumberRestrictions
    $ case x of
        Nothing -> sl_obj_prop op
        Just y -> sl_max (sl_obj_prop op) (sl_desc y)

slLFB :: Maybe Relation -> ListFrameBit -> OWLSub
slLFB mr lfb = case lfb of
    ExpressionBit anl -> foldl sl_max sl_bottom $ map (sl_desc . snd) anl
    ObjectBit anl -> sl_max (case fromMaybe (error "relation needed") mr of
        EDRelation Disjoint -> requireAddFeatures sl_bottom
        _ -> sl_bottom) $ foldl sl_max sl_bottom $ map (sl_obj_prop . snd) anl
    DataBit anl -> sl_max (case fromMaybe (error "relation needed") mr of
        EDRelation Disjoint -> requireAddFeatures sl_bottom
        _ -> sl_bottom) $ foldl sl_max sl_bottom $ map (sl_data_prop . snd) anl
    IndividualSameOrDifferent _ -> requireNominals sl_bottom
    ObjectCharacteristics anl -> foldl sl_max sl_bottom
        $ map (\ c -> case c of
              Transitive -> requireRoleTransitivity sl_bottom
              Reflexive -> requireAddFeatures sl_bottom
              Irreflexive -> requireAddFeatures sl_bottom
              Asymmetric -> requireAddFeatures sl_bottom
              _ -> sl_bottom) $ map snd anl
    DataPropRange anl -> foldl sl_max sl_bottom $ map (sl_data_range . snd) anl
    _ -> sl_bottom

slAFB :: AnnFrameBit -> OWLSub
slAFB afb = case afb of
    DatatypeBit dr -> sl_data_range dr
    ClassDisjointUnion cel -> foldl sl_max sl_bottom $ map sl_desc cel
    ClassHasKey opl dpl -> sl_max (foldl sl_max sl_bottom $ map sl_obj_prop opl)
            (foldl sl_max sl_bottom $ map sl_data_prop dpl)
    ObjectSubPropertyChain opl -> requireComplexRoleInclusions
        $ requireRoleHierarchy $ foldl sl_max sl_bottom $ map sl_obj_prop opl
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
    ClassEntity ce -> sl_max (slFB fb) (sl_desc ce)
    ObjectEntity o -> sl_max (slFB fb) (sl_obj_prop o)
    SimpleEntity e@(Entity ty ent) -> case ty of
        DataProperty -> requireDatatype $ sl_max (slFB fb) (sl_data_prop ent)
        _ -> sl_max (sl_ent e) (slFB fb)

slFrame :: Frame -> OWLSub
slFrame = foldl sl_max sl_bottom . map slAxiom . getAxioms

sl_o_doc :: OntologyDocument -> OWLSub
sl_o_doc = foldl sl_max sl_bottom . map slFrame . ontFrames . ontology

sl_sig :: Sign -> OWLSub
sl_sig sig = if Set.size (dataProperties sig) == 0
    && Set.size (datatypes sig) == 0
    then sl_bottom else requireDatatype sl_bottom

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
