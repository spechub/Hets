{- |
Module      :  $Header$
Description :  abstract syntax of CASL specification libraries
Copyright   :  (c) Klaus Luettich, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt
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
import Common.IRI
import Common.AS_Annotation
import Common.LibName

import Logic.Grothendieck (G_basic_spec)
import Logic.Logic

import Syntax.AS_Architecture
import Syntax.AS_Structured

import Framework.AS
import Framework.ATC_Framework ()

data LIB_DEFN = Lib_defn LibName [Annoted LIB_ITEM] Range [Annotation]
                {- pos: "library"
                list of annotations is parsed preceding the first LIB_ITEM
                the last LIB_ITEM may be annotated with a following comment
                the first LIB_ITEM cannot be annotated -}
                deriving Show

{- for information on the list of Pos see the documentation in
   AS_Structured.hs and AS_Architecture.hs -}

data LIB_ITEM = Spec_defn SPEC_NAME GENERICITY (Annoted SPEC) Range
              -- pos: "spec", "=", opt "end"
              | View_defn VIEW_NAME GENERICITY VIEW_TYPE [G_mapping] Range
              -- pos: "view", ":", opt "=", opt "end"
              | Align_defn ALIGN_NAME (Maybe ALIGN_ARITIES) ALIGN_TYPE
                [CORRESPONDENCE] Range
              | Module_defn MODULE_NAME MODULE_TYPE RESTRICTION_SIGNATURE Range
              {- G_symb_items_list is RESTRICTION-SIGNATURE
              TODO: CONSERVATIVE? -}
              | Arch_spec_defn ARCH_SPEC_NAME (Annoted ARCH_SPEC) Range
              -- pos: "arch", "spec", "=", opt "end"
              | Unit_spec_defn SPEC_NAME UNIT_SPEC Range
              -- pos: "unit", "spec", "=", opt "end"
              | Ref_spec_defn SPEC_NAME REF_SPEC Range
              -- pos: "ref", "spec", "=", opt "end"
              | Download_items LibName DownloadItems Range
              -- pos: "from", "get", "|->", commas, opt "end"
              | Logic_decl LogicDescr Range
              -- pos:  "logic", Logic_name
              | Newlogic_defn LogicDef Range
              -- pos:  "newlogic", Logic_name, "=", opt "end"
              | Newcomorphism_defn ComorphismDef Range
              -- pos: "newcomorphism", Comorphism_name, "=", opt "end"
                deriving Show

{- Item maps are the documented CASL renamed entities whereas a unique item
contains the new target name of the single arbitrarily named item from the
downloaded library. -}
data DownloadItems =
    ItemMaps [ItemNameMap]
  | UniqueItem IRI
    deriving Show

data GENERICITY = Genericity PARAMS IMPORTED Range deriving Show
                  -- pos: many of "[","]" opt ("given", commas)

emptyGenericity :: GENERICITY
emptyGenericity = Genericity (Params []) (Imported []) nullRange

data PARAMS = Params [Annoted SPEC] deriving Show

data IMPORTED = Imported [Annoted SPEC] deriving Show

data VIEW_TYPE = View_type (Annoted SPEC) (Annoted SPEC) Range deriving Show
                 -- pos: "to"

data ALIGN_TYPE = Align_type (Annoted SPEC) (Annoted SPEC) Range deriving Show

data MODULE_TYPE = Module_type (Annoted SPEC) (Annoted SPEC) Range deriving Show

data ALIGN_ARITIES = Align_arities ALIGN_ARITY ALIGN_ARITY deriving (Show, Eq)

data ALIGN_ARITY = AA_InjectiveAndTotal | AA_Injective | AA_Total
                 | AA_NeitherInjectiveNorTotal
                   deriving (Show, Eq)

data ItemNameMap =
    ItemNameMap IRI (Maybe IRI)
    deriving (Show, Eq)

makeLogicItem :: Language lid => lid -> Annoted LIB_ITEM
makeLogicItem lid = emptyAnno $ Logic_decl
  (nameToLogicDescr $ Logic_name
   (language_name lid) Nothing Nothing) nullRange

makeSpecItem :: SPEC_NAME -> Annoted SPEC -> Annoted LIB_ITEM
makeSpecItem sn as =
    emptyAnno $ Spec_defn sn emptyGenericity as nullRange

fromBasicSpec :: LibName -> SPEC_NAME -> G_basic_spec -> LIB_DEFN
fromBasicSpec ln sn gbs =
    Lib_defn ln [makeSpecItem sn $ makeSpec gbs] nullRange []
