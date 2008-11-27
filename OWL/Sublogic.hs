{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Description :  Sublogics for OWL
Copyright   :  (c) Dominik Luecke, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Here is the place where the class Logic is instantiated for OWL DL.
__SROIQ__
-}

module OWL.Sublogic
    (
     OWL_SL(..)
    ,NumberRestrictions(..)
    ,OWLDatatypes(..)
    ,sl_top
    ,sl_bottom
    ,sl_max
    ,sl_name
    ,sl_basic_spec
    ,sl_o_file
    ,sl_sig
    ,sl_mor
    ,pr_o_file
    ,pr_sig
    ,pr_mor
    )
    where

import OWL.AS
import OWL.Morphism
import OWL.Sign
import Common.DefaultMorphism

import qualified Data.Set as Set

data NumberRestrictions = None | Unqualified | Qualified
                        deriving (Show, Eq, Ord)

data OWLDatatypes = OWLNoDatatypes | OWLDatatypes
               deriving (Show, Eq, Ord)

data OWL_SL = OWL_SL
            {
              numberRestrictions :: NumberRestrictions
            , nominals :: Bool
            , inverseRoles :: Bool
            , roleTransitivity :: Bool
            , roleHierarchy :: Bool
            , complexRoleInclusions :: Bool
            , addFeatures :: Bool
            , datatype :: OWLDatatypes
            } deriving (Show, Eq, Ord)

-- | sROIQ(D)
sl_top :: OWL_SL
sl_top = OWL_SL
      {
        numberRestrictions = Qualified
      , nominals = True
      , inverseRoles = True
      , roleTransitivity = True
      , roleHierarchy = True
      , complexRoleInclusions = True
      , addFeatures = True
      , datatype = OWLDatatypes
      }

-- ALC
sl_bottom :: OWL_SL
sl_bottom = OWL_SL
            {
              numberRestrictions = None
            , nominals = False
            , inverseRoles = False
            , roleTransitivity = False
            , roleHierarchy = False
            , complexRoleInclusions = False
            , addFeatures = False
            , datatype = OWLNoDatatypes
            }


sl_max :: OWL_SL -> OWL_SL -> OWL_SL
sl_max sl1 sl2 =
    OWL_SL
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
    , datatype = max (datatype sl1)
                  (datatype sl2)
    }

-- | Naming for Description Logics
sl_name :: OWL_SL -> String
sl_name sl =
    (if (complexRoleInclusions sl || addFeatures sl)
       then
           concat $
                  [
                   if (addFeatures sl) then "s" else ""
                  ,"R"
                  ]
       else
           concat $
                  [
                   if (roleTransitivity sl) then "S" else "ALC"
                  ,if (roleHierarchy sl) then "H" else ""
                  ]
           )
    ++
    (concat $
     [
      if (nominals sl)         then "O" else ""
     ,if (inverseRoles sl)     then "I" else ""
     ,case numberRestrictions sl of
        Qualified   -> "Q"
        Unqualified -> "N"
        None        -> ""
     ,if (datatype sl == OWLDatatypes) then "(D)" else ""
     ])

requireQualNumberRestrictions :: OWL_SL -> OWL_SL
requireQualNumberRestrictions sl = sl
                                   {
                                     numberRestrictions = Qualified
                                   }

requireNumberRestrictions :: OWL_SL -> OWL_SL
requireNumberRestrictions sl =
    if (numberRestrictions sl /= Qualified)
       then
           sl
           {
             numberRestrictions = Unqualified
           }
       else
           sl

requireRoleTransitivity :: OWL_SL -> OWL_SL
requireRoleTransitivity sl = sl
                             {
                               roleTransitivity = True
                             }

requireRoleHierarchy :: OWL_SL -> OWL_SL
requireRoleHierarchy sl = sl
                          {
                            roleHierarchy = True
                          }

requireComplexRoleInclusions :: OWL_SL -> OWL_SL
requireComplexRoleInclusions sl =
    (requireRoleHierarchy $ requireRoleTransitivity sl)
    {
      complexRoleInclusions = True
    }

requireAddFeatures :: OWL_SL -> OWL_SL
requireAddFeatures sl =
    (requireComplexRoleInclusions sl)
    {
      addFeatures = True
    }

requireNominals :: OWL_SL -> OWL_SL
requireNominals sl = sl
                     {
                       nominals = True
                     }

requireInverseRoles :: OWL_SL -> OWL_SL
requireInverseRoles sl = sl
                         {
                           inverseRoles = True
                         }

requireDatatype :: OWL_SL -> OWL_SL
requireDatatype sl = sl
                      {
                        datatype = OWLDatatypes
                      }

-- Sublogics
sl_basic_spec :: Sentence -> OWL_SL
sl_basic_spec sen  =
    case sen of
      OWLAxiom ax -> sl_ax ax
      OWLFact  ax -> sl_ax ax

sl_ax :: Axiom -> OWL_SL
sl_ax ax =
    case ax of
      PlainAxiom _ pax -> sl_p_ax pax
      EntityAnno _    -> sl_bottom

sl_p_ax :: PlainAxiom -> OWL_SL
sl_p_ax pax =
    case pax of
      SubClassOf sub super -> sl_max (sl_desc sub) (sl_desc super)
      EquivOrDisjointClasses _ desl ->
          foldl sl_max sl_bottom $ map sl_desc desl
      DisjointUnion _ desl ->
          foldl sl_max sl_bottom $ map sl_desc desl
      SubObjectPropertyOf sub prop ->
          requireRoleHierarchy $
          sl_max (sl_sub_obj_prop sub) (sl_obj_prop prop)
      SubDataPropertyOf sub prop ->
          requireDatatype $ requireRoleHierarchy $
          sl_max (sl_data_prop sub) (sl_data_prop prop)
      EquivOrDisjointObjectProperties c desc ->
          (\x -> case c of
                   Disjoint -> requireAddFeatures x
                   _        -> x
          ) $ foldl sl_max sl_bottom $ map sl_obj_prop desc
      EquivOrDisjointDataProperties c desc ->
          requireDatatype $
             (\x -> case c of
                      Disjoint -> requireAddFeatures x
                      _        -> x
             ) $ foldl sl_max sl_bottom $ map sl_data_prop desc
      ObjectPropertyDomainOrRange _ oprop descr ->
          sl_max (sl_obj_prop oprop) (sl_desc descr)
      DataPropertyDomainOrRange oprop descr ->
          requireDatatype $
          sl_max (case oprop of
                    DataDomain desc  -> sl_desc desc
                    DataRange rn     -> sl_data_range rn
                 ) (sl_data_prop descr)
      InverseObjectProperties o1 o2 ->
          requireInverseRoles $ sl_max (sl_obj_prop o1) (sl_obj_prop o2)
      ObjectPropertyCharacter k o ->
          (\x -> case k of
                   Transitive  -> requireRoleTransitivity x
                   Reflexive   -> requireAddFeatures x
                   Irreflexive -> requireAddFeatures x
                   Asymmetric  -> requireAddFeatures x
                   _           -> x
          ) $ sl_obj_prop o
      FunctionalDataProperty dp ->
          requireDatatype $ sl_data_prop dp
      SameOrDifferentIndividual _ _ ->
          requireNominals $ sl_bottom
      ClassAssertion _ descr ->
          case descr of
            ObjectComplementOf (ObjectValuesFrom _ prop desc) ->
                requireAddFeatures $ sl_max (sl_obj_prop prop) (sl_desc desc)
            ObjectComplementOf (ObjectHasValue prop _)  ->
                requireAddFeatures $ sl_obj_prop prop
            ObjectComplementOf (ObjectCardinality card)  ->
                requireAddFeatures $ sl_card card
            _ -> sl_desc descr
      ObjectPropertyAssertion (Assertion objProp _ _ _)  ->
          sl_obj_prop objProp
      DataPropertyAssertion (Assertion dProp _ _ _)  ->
          sl_data_prop dProp
      Declaration ent -> sl_ent ent

sl_ent :: Entity
       -> OWL_SL
sl_ent (Entity et _) =
    case et of
      Datatype -> requireDatatype $ sl_bottom
      _        -> sl_bottom

sl_data_prop :: DataPropertyExpression
             -> OWL_SL
sl_data_prop _ = requireDatatype $ sl_bottom

sl_data_range :: DataRange
              -> OWL_SL
sl_data_range rn =
    requireDatatype $
    case rn of
      DRDatatype _            -> sl_bottom
      DataComplementOf c      -> sl_data_range c
      DataOneOf _             -> requireNominals $ sl_bottom
      DatatypeRestriction c _ -> sl_data_range c

sl_desc :: Description -> OWL_SL
sl_desc des =
    case des of
      OWLClassDescription _    -> sl_bottom
      ObjectJunction _ dec     -> foldl sl_max sl_bottom $ map sl_desc dec
      ObjectComplementOf dec   -> sl_desc dec
      ObjectOneOf _            -> requireNominals $ sl_bottom
      ObjectValuesFrom _ o d   -> sl_max (sl_obj_prop o) (sl_desc d)
      ObjectExistsSelf o       -> requireAddFeatures $ sl_obj_prop o
      ObjectHasValue o _       -> sl_obj_prop o
      ObjectCardinality c      -> sl_card c
      DataValuesFrom _ d ds dr -> requireDatatype $
             sl_max (sl_data_range dr)
             $ sl_max (sl_data_prop d)
             (foldl sl_max sl_bottom$
              map sl_data_prop ds)
      DataHasValue d _         -> requireDatatype $ sl_data_prop d
      DataCardinality c        -> requireDatatype $ sl_d_card c

sl_d_card :: Cardinality DataPropertyExpression DataRange
          -> OWL_SL
sl_d_card (Cardinality _ _ dp x) =
    case x of
      Nothing -> requireDatatype $
                 requireNumberRestrictions $
                 sl_data_prop dp
      Just y  -> requireDatatype $
                 requireQualNumberRestrictions $
                 sl_max (sl_data_prop dp) (sl_data_range y)

sl_card :: Cardinality ObjectPropertyExpression Description
          -> OWL_SL
sl_card (Cardinality _ _ op x) =
    case x of
      Nothing -> requireNumberRestrictions $
                 sl_obj_prop op
      Just y  -> requireQualNumberRestrictions $
                 sl_max (sl_obj_prop op) (sl_desc y)

sl_sub_obj_prop :: SubObjectPropertyExpression
                -> OWL_SL
sl_sub_obj_prop s =
    case s of
      OPExpression e -> requireRoleHierarchy $ sl_obj_prop e
      SubObjectPropertyChain e -> requireComplexRoleInclusions $
                                  foldl sl_max sl_bottom $
                                  map sl_obj_prop e

sl_obj_prop :: ObjectPropertyExpression
            -> OWL_SL
sl_obj_prop o =
    case o of
      OpURI _     -> sl_bottom
      InverseOp p -> requireInverseRoles $ sl_obj_prop p

sl_o_file :: OntologyFile -> OWL_SL
sl_o_file o = foldl sl_max sl_bottom $ map sl_ax $ axiomsList $ ontology o

sl_sig :: Sign -> OWL_SL
sl_sig sig =
    if ((Set.size $ dataValuedRoles sig) == 0 &&
       (Set.size $ datatypes sig) == 0)
     then
         sl_bottom
     else
         requireDatatype $ sl_bottom

sl_mor :: OWL_Morphism -> OWL_SL
sl_mor mor = sl_max (sl_sig $ domOfDefaultMorphism mor)
             (sl_sig $ codOfDefaultMorphism mor)

-- projections along sublogics
pr_mor :: OWL_SL -> OWL_Morphism -> OWL_Morphism
pr_mor s a =
    a
    {
      domOfDefaultMorphism = pr_sig s $ domOfDefaultMorphism a
    , codOfDefaultMorphism = pr_sig s $ codOfDefaultMorphism a
    }

pr_sig :: OWL_SL -> Sign -> Sign
pr_sig s a =
    if (datatype s == OWLNoDatatypes)
       then
           a
           {
             datatypes       = Set.empty
           , dataValuedRoles = Set.empty
           }
       else
           a

pr_o_file :: OWL_SL -> OntologyFile -> OntologyFile
pr_o_file s a =
    let
        o = (ontology a)
            {
              axiomsList = filter (\x -> s >= sl_ax x) $ axiomsList $
                           ontology a
            }
    in
      a
      {
        ontology = o
      }