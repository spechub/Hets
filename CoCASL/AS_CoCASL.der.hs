{- |
Module      :  $Header$
Description :  Abstract syntax for CoCASL
Copyright   :  (c) T.Mossakowski, C.Maeder, Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hausmann@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Abstract syntax for CoCASL, the coalgebraic extension of CASL
  Only the added syntax is specified
-}

module CoCASL.AS_CoCASL where

import Common.Id
import Common.AS_Annotation
import CASL.AS_Basic_CASL

-- DrIFT command
{-! global: GetRange !-}

type C_BASIC_SPEC = BASIC_SPEC C_BASIC_ITEM C_SIG_ITEM C_FORMULA

type AnModFORM = Annoted (FORMULA C_FORMULA)

data C_BASIC_ITEM = CoFree_datatype [Annoted CODATATYPE_DECL] Range
                   -- pos: free, type, semi colons
                  | CoSort_gen [Annoted (SIG_ITEMS C_SIG_ITEM C_FORMULA)] Range
                   -- pos: generated, opt. braces
                  deriving Show

data C_SIG_ITEM = CoDatatype_items [Annoted CODATATYPE_DECL] Range
                 -- type, semi colons
                  deriving Show

data CODATATYPE_DECL = CoDatatype_decl SORT [Annoted COALTERNATIVE] Range
                     -- pos: "::=", "|"s
                       deriving Show

data COALTERNATIVE = Co_construct OpKind (Maybe OP_NAME) [COCOMPONENTS] Range
                   -- True if Total, pos: "(", semi colons, ")"
                 | CoSubsorts [SORT] Range
                   -- pos: sort, commas
                  deriving Show

data COCOMPONENTS = CoSelect [OP_NAME] OP_TYPE Range
                  -- pos: commas, colon
                  deriving Show

data MODALITY = Simple_mod SIMPLE_ID | Term_mod (TERM C_FORMULA)
             deriving (Eq, Ord, Show)

data C_FORMULA = BoxOrDiamond Bool MODALITY (FORMULA C_FORMULA) Range
               -- The identifier and the term specify the kind of the modality
               -- pos: "[]" or  "<>", True if Box, False if Diamond
               | CoSort_gen_ax [SORT] [OP_SYMB] Bool
               -- flag: belongs to a cofree type and hence is cofreeness axiom?
             deriving (Eq, Ord, Show)
