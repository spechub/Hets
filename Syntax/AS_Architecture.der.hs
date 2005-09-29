{-| 
   
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable(imports Syntax.AS_Structured)

These data structures describe the abstract syntax tree for heterogenous 
   architectural specifications in HetCASL.
   Follows Sect. II:2.2.4 of the CASL Reference Manual.
-}

module Syntax.AS_Architecture where

import Common.Id
import Common.AS_Annotation

import Syntax.AS_Structured

-- Drift directive:
{-! global : UpPos !-}

data ARCH_SPEC_DEFN = Arch_spec_defn ARCH_SPEC_NAME (Annoted ARCH_SPEC) Range
                      -- pos: "arch","spec","=",opt "end"
                      deriving (Show)

data ARCH_SPEC = Basic_arch_spec [Annoted UNIT_DECL_DEFN]
                                 (Annoted UNIT_EXPRESSION) Range
                 -- pos: "unit","result"
               | Arch_spec_name ARCH_SPEC_NAME
               | Group_arch_spec (Annoted ARCH_SPEC) Range
                 -- pos: "{","}"
                 deriving (Show)


data UNIT_DECL_DEFN = Unit_decl UNIT_NAME REF_SPEC [Annoted UNIT_TERM] Range
                      -- pos: ":", opt ("given"; Annoted holds pos of commas)
                    | Unit_defn UNIT_NAME UNIT_EXPRESSION Range
                      -- pos: "="
                      deriving (Show)

data UNIT_SPEC_DEFN = Unit_spec_defn SPEC_NAME UNIT_SPEC Range
                      -- pos: "unit","spec","=", opt "end"
                      deriving (Show)

data UNIT_SPEC = Unit_type [Annoted SPEC] (Annoted SPEC) Range
                 -- pos: opt "*"s , "->"
               | Spec_name SPEC_NAME
               | Closed_unit_spec UNIT_SPEC Range
                 -- pos: "closed"
                 deriving (Show)

data REF_SPEC = Unit_spec UNIT_SPEC
              | Refinement Bool UNIT_SPEC [G_mapping] REF_SPEC Range
                -- false means "behaviourally"
              | Arch_unit_spec (Annoted ARCH_SPEC) Range 
                 -- pos: "arch","spec"
                 -- The ARCH_SPEC has to be surrounded with braces and
                 -- after the opening brace is a [Annotation] allowed
              | Compose_ref [REF_SPEC] Range
                 -- pos: "then"
              | Component_ref [UNIT_REF] Range
                -- pos "{", commas and "}"
                 deriving (Show)

data UNIT_REF = Unit_ref UNIT_NAME REF_SPEC Range 
                 -- pos: ":"
                 deriving (Show)

data UNIT_EXPRESSION = Unit_expression [UNIT_BINDING] (Annoted UNIT_TERM) Range
                       -- pos: opt "lambda",semi colons, "."
                       deriving (Show)

data UNIT_BINDING = Unit_binding UNIT_NAME UNIT_SPEC Range
                    -- pos: ":"
                    deriving (Show) 

data UNIT_TERM = Unit_reduction (Annoted UNIT_TERM) RESTRICTION
               | Unit_translation (Annoted UNIT_TERM) RENAMING 
               | Amalgamation [Annoted UNIT_TERM] Range
                 -- pos: "and"s
               | Local_unit [Annoted UNIT_DECL_DEFN] (Annoted UNIT_TERM) Range 
                 -- pos: "local", "within"
               | Unit_appl UNIT_NAME [FIT_ARG_UNIT] Range
                 -- pos: many of "[","]"
               | Group_unit_term (Annoted UNIT_TERM) Range
                 -- pos: "{","}"
                 deriving (Show)

data FIT_ARG_UNIT = Fit_arg_unit (Annoted UNIT_TERM) [G_mapping] Range 
                    -- pos: opt "fit"
                    deriving (Show)

type ARCH_SPEC_NAME = SIMPLE_ID
type UNIT_NAME = SIMPLE_ID
