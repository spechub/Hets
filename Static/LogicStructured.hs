{-| 
   
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Pascal Schmidt, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

Description :  calculate sublogic of structured items

This module provides routines to calculate the sublogic of a structured
   item - a structured specification, a view, an architectural
   specification, or a library. The calculation succeeds for homogenous
   items (only one language occuring inside) and returns Nothing otherwise.

-}

-----------------------------------------------------------------------------
-- Export declarations
-----------------------------------------------------------------------------

module Static.LogicStructured ( -- SPEC_DEFN -> Maybe G_Sublogics
                         min_sublogic_spec_defn,
                         
                         -- VIEW_DEFN -> Maybe G_Sublogics
                         min_sublogic_view_defn,

                         -- LIB_DEFN -> Maybe G_Sublogics
                         min_sublogic_lib_defn,
                         
                         -- ARCH_SPEC_DEFN -> Maybe G_Sublogics
                         min_sublogic_arch_spec_defn,
                         
                         -- UNIT_SPEC_DEFN -> Maybe G_Sublogics
                         min_sublogic_unit_spec_defn

                       ) where

-----------------------------------------------------------------------------
-- Imports from other modules
-----------------------------------------------------------------------------

import Maybe ( isJust )
import Utils ( IgnoreMaybe(..), dropIgnore, toIgnore, toMaybe )
import AS_Structured
import AS_Architecture
import qualified AS_Library
import AS_Annotation ( Annoted(..) )
import Logic ( coerce, join, language_name, min_sublogic_symb_items,
               min_sublogic_symb_map_items, min_sublogic_basic_spec,
               top )
import Grothendieck( G_basic_spec(..), G_sublogics(..),
                     G_symb_items_list(..), G_symb_map_items_list(..) )

-----------------------------------------------------------------------------
-- Module implementation
--
-- Computations on Maybe/IgnoreMaybe G_sublogics datatype
-----------------------------------------------------------------------------

-- extension of meet from Logic.hs to Maybe G_sublogics
-- coerce stuff done by Till
--
top_logics :: Maybe G_sublogics -> Maybe G_sublogics -> Maybe G_sublogics
top_logics Nothing _ = Nothing
top_logics _ Nothing = Nothing
top_logics (Just (G_sublogics a (al::sublogics))) (Just (G_sublogics b bl)) =
  if ((language_name a)==(language_name b)) then
    case (coerce a b bl)::Maybe sublogics of
      Just bl1 -> Just (G_sublogics a (join al bl1))
      Nothing  -> Nothing
  else
    Nothing

-- version of top_logics that ignores IgnoreNothing argument(s)
--
top_logics_ign :: IgnoreMaybe G_sublogics -> IgnoreMaybe G_sublogics
                  -> IgnoreMaybe G_sublogics
top_logics_ign IgnoreNothing _ = IgnoreNothing
top_logics_ign _ IgnoreNothing = IgnoreNothing
top_logics_ign a b = toIgnore $ top_logics (toMaybe a) (toMaybe b)

-- compute Maybe G_sublogics from a list by folding top_logics
--
map_logics :: [Maybe G_sublogics] -> Maybe G_sublogics
map_logics []    = Nothing
map_logics (h:t) = foldr top_logics h t

-- version of map_logics handling IgnoreNothing inputs
-- list with only IgnoreNothing elements turns to single IgnoreNothing
--
map_logics_ign :: [IgnoreMaybe G_sublogics] -> IgnoreMaybe G_sublogics
map_logics_ign l = let
                     tryDrop = dropIgnore l
                   in
                     if ((length tryDrop)==0) then
                       IgnoreNothing
                     else
                       toIgnore $ map_logics tryDrop

-----------------------------------------------------------------------------
-- Computations functions simply recurse down into all datatype members.
-- All functions ignore Pos lists and names since they have no impact on
-- the sublogic needed. Other elements are ignored if they also have no
-- impact on the sublogic.
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- Functions to compute minimally needed sublogics for datatypes from
-- AS_Structured module
-----------------------------------------------------------------------------

-- calls function from Logic.hs to calculate sublogic of Basic_spec
--
sl_spec :: SPEC -> Maybe G_sublogics
sl_spec (Basic_spec (G_basic_spec i b)) = 
  Just (G_sublogics i (min_sublogic_basic_spec i b))
sl_spec (Translation s r) =
  toMaybe $ top_logics_ign (toIgnore $ sl_spec $ item s) (sl_renaming r)
sl_spec (Reduction s r) =
  toMaybe $ top_logics_ign (toIgnore $ sl_spec $ item s) (sl_restriction r)
sl_spec (Union l _) = map_logics $ map sl_spec $ map item l
sl_spec (Extension l _) = map_logics $ map sl_spec $ map item l
sl_spec (Free_spec s _) = sl_spec $ item s
sl_spec (Local_spec a b _) = top_logics (sl_spec $ item a)
                                        (sl_spec $ item b)
sl_spec (Group s _) = sl_spec $ item s
sl_spec (Spec_inst _ l) = map_logics $ map sl_fit_arg $ map item l
sl_spec (Qualified_spec _ s _) = sl_spec $ item s

sl_renaming :: RENAMING -> IgnoreMaybe G_sublogics
sl_renaming (Renaming l _) = map_logics_ign $ map sl_g_mapping l

sl_restriction :: RESTRICTION -> IgnoreMaybe G_sublogics
sl_restriction (Hidden l _) = map_logics_ign $ map sl_g_hiding l
sl_restriction (Revealed l _) = toIgnore $ sl_g_symb_map_items_list l

sl_g_mapping :: G_mapping -> IgnoreMaybe G_sublogics
sl_g_mapping (G_symb_map l) = toIgnore $ sl_g_symb_map_items_list l
sl_g_mapping (G_logic_translation c) = sl_logic_code c

sl_g_hiding :: G_hiding -> IgnoreMaybe G_sublogics
sl_g_hiding (G_symb_list l) = toIgnore $ sl_g_symb_items_list l
sl_g_hiding (G_logic_projection c) = sl_logic_code c

-- find out whether a Logic_code really changes the language
-- see Trac for possible extensions for (isJust enc) and
-- (try!=src) cases
--
sl_logic_code :: Logic_code -> IgnoreMaybe G_sublogics
sl_logic_code (Logic_code enc src trg _) =
  if (isJust enc) then
    RealNothing             -- encoding given, could change sublogic
  else
    if (isJust src) then
      if (isJust trg) then
        if (trg==src) then
          IgnoreNothing     -- projection/translation that does nothing
        else
          RealNothing       -- projection/translation that changes things
      else
        IgnoreNothing       -- just source logic given,
    else
      IgnoreNothing         -- empty projection/translation, shouldn't happen

-- calls function from Logic.hs to compute sublogics
--
sl_g_symb_items_list :: G_symb_items_list -> Maybe G_sublogics
sl_g_symb_items_list (G_symb_items_list i l) =
  Just (G_sublogics i (foldr join top ((map (min_sublogic_symb_items i)) l)))

-- calls function from Logic.hs to compute sublogics
-- 
sl_g_symb_map_items_list :: G_symb_map_items_list -> Maybe G_sublogics
sl_g_symb_map_items_list (G_symb_map_items_list i l) =
  Just
  (G_sublogics i (foldr join top ((map (min_sublogic_symb_map_items i)) l)))
  
sl_spec_defn :: SPEC_DEFN -> Maybe G_sublogics
sl_spec_defn (Spec_defn _ g s _) = top_logics (sl_genericity g)
                                              (sl_spec $ item s)

sl_genericity :: GENERICITY -> Maybe G_sublogics
sl_genericity (Genericity p i _) = top_logics (sl_params p) (sl_imported i)

sl_params :: PARAMS -> Maybe G_sublogics
sl_params (Params l) = map_logics $ map sl_spec $ map item l

sl_imported :: IMPORTED -> Maybe G_sublogics
sl_imported (Imported l) = map_logics $ map sl_spec $ map item l

sl_fit_arg :: FIT_ARG -> Maybe G_sublogics
sl_fit_arg (Fit_spec s l _) = top_logics (sl_spec $ item s)
                                         (sl_g_symb_map_items_list l)
sl_fit_arg (Fit_view _ l _ _) = map_logics $ map sl_fit_arg $ map item l

sl_view_defn :: VIEW_DEFN -> Maybe G_sublogics
sl_view_defn (View_defn _ g t l _) = toMaybe $ map_logics_ign
  ((toIgnore $ sl_genericity g):(toIgnore $ sl_view_type t):
    (map sl_g_mapping l))

sl_view_type :: VIEW_TYPE -> Maybe G_sublogics
sl_view_type (View_type a b _) = top_logics (sl_spec $ item a)
                                            (sl_spec $ item b)

-----------------------------------------------------------------------------
-- Functions to compute minimally needed sublogics for datatypes from
-- AS_Library module
-----------------------------------------------------------------------------

sl_lib_defn :: AS_Library.LIB_DEFN -> Maybe G_sublogics
sl_lib_defn (AS_Library.Lib_defn _ l _ _) =
  map_logics $ map sl_lib_item $ map item l

-- sl_lib_item returns Nothing on Download_items because it is only
-- a list of names with insufficient information to calculate G_sublogics
-- sl_lib_item returns Nothing on Logic because the target logic of
-- logic projection/translation is not convertible to G_sublogics yet
--
sl_lib_item :: AS_Library.LIB_ITEM -> Maybe G_sublogics
sl_lib_item (AS_Library.Spec_defn _ g s _) =
  top_logics (sl_genericity g) (sl_spec $ item s)
sl_lib_item (AS_Library.View_defn _ g t l _) = toMaybe $ map_logics_ign
  ((toIgnore $ sl_genericity g):(toIgnore $ sl_view_type t):
    (map sl_g_mapping l))
sl_lib_item (AS_Library.Arch_spec_defn _ s _) = sl_arch_spec $ item s
sl_lib_item (AS_Library.Unit_spec_defn _ s _) = sl_unit_spec s
sl_lib_item (AS_Library.Download_items _ l _) = Nothing
sl_lib_item (AS_Library.Logic n _) = Nothing

-----------------------------------------------------------------------------
-- Functions to compute minimally needed sublogics for datatypes from
-- AS_Architecture module
-----------------------------------------------------------------------------

sl_arch_spec_defn :: ARCH_SPEC_DEFN -> Maybe G_sublogics
sl_arch_spec_defn (Arch_spec_defn _ s _) = sl_arch_spec $ item s

-- sl_arch_spec returns Nothing on Arch_spec_name because the name
-- does not carry enough information needed to calculate G_sublogics
--
sl_arch_spec :: ARCH_SPEC -> Maybe G_sublogics
sl_arch_spec (Basic_arch_spec l e _) =  map_logics
  ((sl_unit_expression $ item e):(map sl_unit_decl_defn $ map item l))
sl_arch_spec (Arch_spec_name _) = Nothing
sl_arch_spec (Group_arch_spec s _) = sl_arch_spec $ item s

sl_unit_decl_defn :: UNIT_DECL_DEFN -> Maybe G_sublogics
sl_unit_decl_defn (Unit_decl _ s l _) =
  map_logics ((sl_unit_spec s):(map sl_unit_term $ map item l))
sl_unit_decl_defn (Unit_defn _ e _) = sl_unit_expression e

sl_unit_spec_defn :: UNIT_SPEC_DEFN -> Maybe G_sublogics
sl_unit_spec_defn (Unit_spec_defn _ s _) = sl_unit_spec s

-- sl_unit_spec returns Nothing on Spec_name because the name does
-- not carry enough information needed to calculate G_sublogics
--
sl_unit_spec :: UNIT_SPEC -> Maybe G_sublogics
sl_unit_spec (Unit_type l s _) =
  map_logics ((sl_spec $ item s):(map sl_spec $ map item l))
sl_unit_spec (Spec_name _) = Nothing
sl_unit_spec (Arch_unit_spec s _) = sl_arch_spec $ item s
sl_unit_spec (Closed_unit_spec s _) = sl_unit_spec s

sl_unit_expression :: UNIT_EXPRESSION -> Maybe G_sublogics
sl_unit_expression (Unit_expression l t _) =
  map_logics ((sl_unit_term $ item t):(map sl_unit_binding l))

sl_unit_binding :: UNIT_BINDING -> Maybe G_sublogics
sl_unit_binding (Unit_binding _ s _) = sl_unit_spec s

sl_unit_term :: UNIT_TERM -> Maybe G_sublogics
sl_unit_term (Unit_reduction t r) = toMaybe $
  top_logics_ign (toIgnore $ sl_unit_term $ item t) (sl_restriction r)
sl_unit_term (Unit_translation t r) = toMaybe $
  top_logics_ign (toIgnore $ sl_unit_term $ item t) (sl_renaming r)
sl_unit_term (Amalgamation l _) = map_logics $ map sl_unit_term $ map item l
sl_unit_term (Local_unit l t _) =
  map_logics ((sl_unit_term $ item t):(map sl_unit_decl_defn $ map item l))
sl_unit_term (Unit_appl _ l _) = map_logics $ map sl_fit_arg_unit l
sl_unit_term (Group_unit_term t _) = sl_unit_term $ item t

sl_fit_arg_unit :: FIT_ARG_UNIT -> Maybe G_sublogics
sl_fit_arg_unit (Fit_arg_unit t l _) =
  top_logics (sl_unit_term $ item t) (sl_g_symb_map_items_list l)

-----------------------------------------------------------------------------
-- Alias exported function to names similar to the calculation functions
-- from Logic.hs, different naming convention in this module since
-- internal functions don't need to have overly verbose names that would
-- make the code hard to read
-----------------------------------------------------------------------------

min_sublogic_spec_defn = sl_spec_defn
min_sublogic_view_defn = sl_view_defn
min_sublogic_lib_defn = sl_lib_defn
min_sublogic_arch_spec_defn = sl_arch_spec_defn
min_sublogic_unit_spec_defn = sl_unit_spec_defn

-----------------------------------------------------------------------------
-- THE END
-----------------------------------------------------------------------------
