------------------------------------------------------------------------------
-- HetCATS/LogicStructured.hs
-- $Id$
-- Authors: Pascal Schmidt
-- Year:    2002
------------------------------------------------------------------------------
{- todo:

  Hochziehen auf strukturierte Ebene
    Maybe(existentiellen Typ G_sublogics aus Grothendieck.hs) verwenden
    AS_Structured.hs, AS_Arch.hs, AS_Library.hs
    Funktionen aus Logic_CASL.hs bzw. Logic.hs verwenden
    Nur für homogene Specs das jeweilige Maximum berechnen
      (Vergleich von Logic-ids mit language_name), ansonsten Nothing

-}

module LogicStructured ( -- AS_Structured.SPEC -> Maybe G_Sublogics
                         min_sublogic_spec,

                         -- AS_Library.LIB_DEFN -> Maybe G_Sublogics
                         min_sublogic_lib

                       ) where

import Maybe
import Id
import AS_Structured
import AS_Architecture
import qualified AS_Library
import AS_Annotation
import Logic
import Grothendieck

{-
top_logics :: G_sublogics -> G_sublogics -> Maybe G_sublogics
top_logics (G_sublogics a al) (G_sublogics b bl) =
  if ((language_name a)==(language_name b)) then
    Just (G_sublogics a (meet al bl))
  else
    Nothing
-}

-- FIXME
-- dummy version of above function
top_logics :: Maybe G_sublogics -> Maybe G_sublogics -> Maybe G_sublogics
top_logics Nothing _ = Nothing
top_logics _ Nothing = Nothing
top_logics (Just a) (Just b) = Just a

map_logics :: [Maybe G_sublogics] -> Maybe G_sublogics
map_logics [] = Nothing
map_logics (h:t) = foldr top_logics h t

-- functions on datatypes from AS_Structured

sl_spec :: SPEC -> Maybe G_sublogics
sl_spec (Basic_spec (G_basic_spec i b)) = 
  Just (G_sublogics i (min_sublogic_basic_spec i b))
sl_spec (Translation s r) = top_logics (sl_spec $ item s) (sl_renaming r)
sl_spec (Reduction s r) = top_logics (sl_spec $ item s) (sl_restriction r)
sl_spec (Union l _) = map_logics $ map sl_spec $ map item l
sl_spec (Extension l _) = map_logics $ map sl_spec $ map item l
sl_spec (Free_spec s _) = sl_spec $ item s
sl_spec (Local_spec a b _) = top_logics (sl_spec $ item a)
                                        (sl_spec $ item b)
sl_spec (Group s _) = sl_spec $ item s
sl_spec (Spec_inst _ l) = map_logics $ map sl_fit_arg $ map item l
sl_spec (Qualified_spec _ s _) = sl_spec $ item s

sl_renaming :: RENAMING -> Maybe G_sublogics
sl_renaming (Renaming l _) = map_logics $ map sl_g_mapping l

sl_restriction :: RESTRICTION -> Maybe G_sublogics
sl_restriction (Hidden l _) = map_logics $ map sl_g_hiding l
sl_restriction (Revealed l _) = sl_g_symb_map_items_list l

sl_g_mapping :: G_mapping -> Maybe G_sublogics
sl_g_mapping (G_symb_map l) = sl_g_symb_map_items_list l
sl_g_mapping (G_logic_translation c) = sl_logic_code c

sl_g_hiding :: G_hiding -> Maybe G_sublogics
sl_g_hiding (G_symb_list l) = sl_g_symb_items_list l
sl_g_hiding (G_logic_projection c) = sl_logic_code c

-- CHECK
-- is this how Logic_code should go into the sublogics calculation,
-- the target logic taking precedence if given, then the encoding
-- if it is given (gives more precise logic than source logic because it
-- also knows the sublogic involved), then source logic with least
-- precedence?
sl_logic_code :: Logic_code -> Maybe G_sublogics
sl_logic_code (Logic_code t n m _) =
  if (isJust m) then
    sl_logic_name $ fromJust m
  else
    if (isJust t) then
      sl_encoding $ fromJust t
    else
      if (isJust n) then
        sl_logic_name $ fromJust n
      else
        Nothing

-- CHECK
-- is the encoding really a sublogic name?
sl_encoding :: Token -> Maybe G_sublogics
sl_encoding x = logic_from_sublogic_name $ tokStr x

-- CHECK
-- is Logic_name t1 (maybe t2) meant as t1 being a language_name
-- and t2 being a sublogic_name?
sl_logic_name :: Logic_name -> Maybe G_sublogics
sl_logic_name (Logic_name t Nothing) = logic_from_name $ tokStr t
sl_logic_name (Logic_name t (Just e)) = sl_encoding e

-- CHECK
-- if I get this right, these function would have to iterate over
-- all instances of Logic and check whether the given encoding
-- string is a member of all_sublogics of the Logic, then run some
-- function turning that sublogic name back into a sublogic type?
-- That would make these: (logic_from_name, logic_from_sublogic_name)
-- part of Logic.hs
-- And then, how do we iterate over all members of a class?
-- Otherwise, to avoid these somewhat ugly (Maybe type) functions,
-- Logic_code/name would have to use something like
--     Logic_code (Maybe sublogics) (Maybe id) (Maybe id) [Pos]
--     Logic_name id (Maybe sublogics)

-- FIXME
-- one of the functions needed for string to logic conversion
-- should return (id,sub) with
--   id  = which logic it is
--   sub = top sublogic for the logic 
logic_from_name :: String -> Maybe G_sublogics
logic_from_name s = Nothing

-- FIXME
-- another needed function
-- should return (id,sub) with
--    sub = sublogic to be found identifical in name to string
--    id  = logic in which this sublogic resides
logic_from_sublogic_name :: String -> Maybe G_sublogics
logic_from_sublogic_name s = Nothing

sl_g_symb_items_list :: G_symb_items_list -> Maybe G_sublogics
sl_g_symb_items_list (G_symb_items_list i l) =
  Just (G_sublogics i (foldr meet top ((map (min_sublogic_symb_items i)) l)))
  
sl_g_symb_map_items_list :: G_symb_map_items_list -> Maybe G_sublogics
sl_g_symb_map_items_list (G_symb_map_items_list i l) =
  Just
  (G_sublogics i (foldr meet top ((map (min_sublogic_symb_map_items i)) l)))
  
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
sl_view_defn (View_defn _ g t l _) =
  map_logics ([sl_genericity g,sl_view_type t] ++ ((map sl_g_mapping) l))

sl_view_type :: VIEW_TYPE -> Maybe G_sublogics
sl_view_type (View_type a b _) = top_logics (sl_spec $ item a)
                                            (sl_spec $ item b)

-- functions on datatypes from AS_Library

sl_lib_defn :: AS_Library.LIB_DEFN -> Maybe G_sublogics
sl_lib_defn (AS_Library.Lib_defn _ l _ _) =
  map_logics $ map sl_lib_item $ map item l

-- FIXME
-- Download_items, how can we know the logic of imported stuff?
sl_lib_item :: AS_Library.LIB_ITEM -> Maybe G_sublogics
sl_lib_item (AS_Library.Spec_defn _ g s _) =
  top_logics (sl_genericity g) (sl_spec $ item s)
sl_lib_item (AS_Library.View_defn _ g t l _) =
  map_logics ((sl_genericity g):(sl_view_type t):((map sl_g_mapping) l))
sl_lib_item (AS_Library.Arch_spec_defn _ s _) = sl_arch_spec $ item s
sl_lib_item (AS_Library.Unit_spec_defn _ s _) = sl_unit_spec s
sl_lib_item (AS_Library.Download_items _ l _) = Nothing
sl_lib_item (AS_Library.Logic n _) = sl_logic_name n

-- functions on types from AS_Architecture

sl_arch_spec_defn :: ARCH_SPEC_DEFN -> Maybe G_sublogics
sl_arch_spec_defn (Arch_spec_defn _ s _) = sl_arch_spec $ item s

-- FIXME
-- how to handle Arch_spec_name which doesn't have info?
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

-- FIXME
-- how to handle Spec_name which doesn't have info?
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
sl_unit_term (Unit_reduction t r) =
  top_logics (sl_unit_term $ item t) (sl_restriction r)
sl_unit_term (Unit_translation t r) =
  top_logics (sl_unit_term $ item t) (sl_renaming r)
sl_unit_term (Amalgamation l _) = map_logics $ map sl_unit_term $ map item l
sl_unit_term (Local_unit l t _) =
  map_logics ((sl_unit_term $ item t):(map sl_unit_decl_defn $ map item l))
sl_unit_term (Unit_appl _ l _) = map_logics $ map sl_fit_arg_unit l
sl_unit_term (Group_unit_term t _) = sl_unit_term $ item t

sl_fit_arg_unit :: FIT_ARG_UNIT -> Maybe G_sublogics
sl_fit_arg_unit (Fit_arg_unit t l _) =
  top_logics (sl_unit_term $ item t) (sl_g_symb_map_items_list l)

-- top level stuff for this module

min_sublogic_spec = sl_spec

min_sublogic_lib = sl_lib_defn
