{- |
Module      :  $Header$
Description :  abstract syntax of CASL specification libraries
Copyright   :  (c) Klaus Luettich, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

Abstract syntax of HetCASL specification libraries
   Follows Sect. II:2.2.5 of the CASL Reference Manual.
-}

module Syntax.AS_Library where

-- DrIFT command:
{-! global: GetRange !-}

import Common.Id
import Common.AS_Annotation
import Common.LibName

import Syntax.AS_Architecture
import Syntax.AS_Structured

data LIB_DEFN = Lib_defn LibName [Annoted LIB_ITEM] Range [Annotation]
                -- pos: "library"
                -- list of annotations is parsed preceding the first LIB_ITEM
                -- the last LIB_ITEM may be annotated with a following comment
                -- the first LIB_ITEM cannot be annotated
                deriving Show

{- for information on the list of Pos see the documentation in
   AS_Structured.hs and AS_Architecture.hs -}

data LIB_ITEM = Spec_defn SPEC_NAME GENERICITY (Annoted SPEC) Range
              -- pos: "spec","=",opt "end"
              | View_defn VIEW_NAME GENERICITY VIEW_TYPE [G_mapping] Range
              -- pos: "view",":",opt "=", opt "end"
              | Arch_spec_defn ARCH_SPEC_NAME (Annoted ARCH_SPEC) Range
              -- pos: "arch","spec","=",opt "end"
              | Unit_spec_defn SPEC_NAME UNIT_SPEC Range
              -- pos: "unit","spec","=", opt "end"
              | Ref_spec_defn SPEC_NAME REF_SPEC Range
              -- pos: "ref","spec","=", opt "end"
              | Download_items  LibName [ITEM_NAME_OR_MAP] Range
              -- pos: "from","get",commas, opt "end"
              | Logic_decl Logic_name Range
              -- pos:  "logic", Logic_name
                deriving Show

data GENERICITY = Genericity PARAMS IMPORTED Range deriving Show
                  -- pos: many of "[","]" opt ("given", commas)

data PARAMS = Params [Annoted SPEC] deriving Show

data IMPORTED = Imported [Annoted SPEC] deriving Show

data VIEW_TYPE = View_type (Annoted SPEC) (Annoted SPEC) Range deriving Show
                 -- pos: "to"

data ITEM_NAME_OR_MAP = Item_name ITEM_NAME
                      | Item_name_map ITEM_NAME ITEM_NAME Range -- pos: "|->"
                        deriving (Show, Eq)

type ITEM_NAME = SIMPLE_ID
