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
import OWL.Sign

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
sl_basic_spec _  = sl_top

sl_o_file :: OntologyFile -> OWL_SL
sl_o_file _ = sl_top

sl_sig :: Sign -> OWL_SL
sl_sig _ = sl_top

sl_mor :: t -> OWL_SL
sl_mor _  = sl_top

-- projections along sublogics
pr_mor :: t -> t1 -> t1
pr_mor _ a = a

pr_sig :: t -> t1 -> t1
pr_sig _ a = a

pr_o_file :: t -> t1 -> t1
pr_o_file _ a = a
