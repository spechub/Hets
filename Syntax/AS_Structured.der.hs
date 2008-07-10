{- |
Module      :  $Header$
Description :  abstract syntax of CASL structured specifications
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

Abstract syntax of HetCASL (heterogeneous) structured specifications
   Follows Sect. II:2.2.3 of the CASL Reference Manual.
-}

module Syntax.AS_Structured where

-- DrIFT command:
{-! global: GetRange !-}

import Common.Id
import Common.AS_Annotation

import Logic.Logic (AnyLogic)
import Logic.Grothendieck
    ( G_basic_spec
    , G_symb_items_list
    , G_symb_map_items_list)

-- for spec-defn and view-defn see AS_Library

data SPEC = Basic_spec G_basic_spec Range
          | EmptySpec Range
          | Translation (Annoted SPEC) RENAMING
          | Reduction (Annoted SPEC) RESTRICTION
          | Union [(Annoted SPEC)] Range
            -- pos: "and"s
          | Extension [(Annoted SPEC)] Range
            -- pos: "then"s
          | Free_spec (Annoted SPEC) Range
            -- pos: "free"
          | Cofree_spec (Annoted SPEC) Range
            -- pos: "cofree"
          | Local_spec (Annoted SPEC) (Annoted SPEC) Range
            -- pos: "local", "within"
          | Closed_spec (Annoted SPEC) Range
            -- pos: "closed"
          | Group (Annoted SPEC) Range
            -- pos: "{","}"
          | Spec_inst SPEC_NAME [Annoted FIT_ARG] Range
            -- pos: many of "[","]"; one balanced pair per FIT_ARG
          | Qualified_spec Logic_name (Annoted SPEC) Range
            -- pos: "logic", Logic_name,":"
          | Data AnyLogic AnyLogic (Annoted SPEC) (Annoted SPEC) Range
            -- pos: "data"
            deriving Show

{- Renaming and Hiding can be performend with intermediate Logic
   mappings / Logic projections.

-}
data RENAMING = Renaming [G_mapping] Range
                -- pos: "with", list of comma pos
                 deriving (Show, Eq)

data RESTRICTION = Hidden [G_hiding] Range
                   -- pos: "hide", list of comma pos
                 | Revealed G_symb_map_items_list Range
                   -- pos: "reveal", list of comma pos
                   deriving (Show, Eq)

data G_mapping = G_symb_map G_symb_map_items_list
               | G_logic_translation Logic_code
                 deriving (Show, Eq)

data G_hiding = G_symb_list G_symb_items_list
               | G_logic_projection Logic_code
                 deriving (Show, Eq)

data FIT_ARG = Fit_spec (Annoted SPEC) [G_mapping] Range
               -- pos: opt "fit"
             | Fit_view VIEW_NAME [Annoted FIT_ARG] Range
               -- annotations before the view keyword are stored in Spec_inst
               deriving Show

type SPEC_NAME = SIMPLE_ID
type VIEW_NAME = SIMPLE_ID

data Logic_code = Logic_code (Maybe Token)
                             (Maybe Logic_name)
                             (Maybe Logic_name) Range
                 -- pos: "logic",<encoding>,":",<src-logic>,"->",<targ-logic>
                 -- one of <encoding>, <src-logic> or <targ-logic>
                 -- must be given (by Just)
                 -- "logic bla"    => <encoding> only
                 -- "logic bla ->" => <src-logic> only
                 -- "logic -> bla" => <targ-logic> only
                 -- "logic bla1 -> bla2" => <src-logic> and <targ-logic>
                 -- -- "logic bla1:bla2"    => <encoding> and <src-logic>
                 -- ^ this notation is not very useful and is not maintained
                 -- "logic bla1:bla2 ->" => <encoding> and <src-logic> (!)
                 -- "logic bla1: ->bla2" => <encoding> and <targ-logic>
                  deriving (Show, Eq)

data Logic_name = Logic_name Token (Maybe Token) deriving (Show, Eq)
