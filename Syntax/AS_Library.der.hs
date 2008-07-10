{- |
Module      :  $Header$
Description :  abstract syntax of CASL specification libraries
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2006
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

import System.Time
import Data.List
import Common.Id
import Common.AS_Annotation

import Syntax.AS_Architecture
import Syntax.AS_Structured


data LIB_DEFN = Lib_defn LIB_NAME [Annoted LIB_ITEM] Range [Annotation]
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
              | Download_items  LIB_NAME [ITEM_NAME_OR_MAP] Range
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

data LIB_NAME = Lib_version
    { getLIB_ID :: LIB_ID
    , libVersion :: VERSION_NUMBER }
    | Lib_id { getLIB_ID :: LIB_ID }

data LIB_ID = Direct_link URL Range
              -- pos: start of URL
            | Indirect_link PATH Range FilePath ClockTime
              -- pos: start of PATH

noTime :: ClockTime
noTime = TOD 0 0

-- | Returns the LIB_ID of a LIB_NAME
getModTime :: LIB_ID -> ClockTime
getModTime li = case li of
    Direct_link _ _ -> noTime
    Indirect_link _ _ _ m -> m

updFilePathOfLibId :: FilePath -> ClockTime -> LIB_ID -> LIB_ID
updFilePathOfLibId fp mt li = case li of
  Direct_link _ _ -> li
  Indirect_link p r _ _ -> Indirect_link p r fp mt

setFilePath :: FilePath -> ClockTime -> LIB_DEFN -> LIB_DEFN
setFilePath fp mt (Lib_defn ln lis r as) =
  Lib_defn ln { getLIB_ID = updFilePathOfLibId fp mt $ getLIB_ID ln } lis r as

data VERSION_NUMBER = Version_number [String] Range deriving (Show, Eq)
                      -- pos: "version", start of first string

type URL = String
type PATH = String

instance Show LIB_ID where
  show (Direct_link s1 _) = s1
  show (Indirect_link s1 _ _ _) = s1

instance Show LIB_NAME where
  show (Lib_version libid (Version_number vs _)) =
      shows libid " version " ++ concat (intersperse "." vs)
  show (Lib_id libid) = show libid

instance Eq LIB_ID where
  Direct_link s1 _ == Direct_link s2 _ = s1 == s2
  Indirect_link s1 _ _ _ == Indirect_link s2 _ _ _ = s1 == s2
  _ == _ = False

instance Ord LIB_ID where
  Direct_link s1 _ <= Direct_link s2 _ = s1 <= s2
  Indirect_link s1 _ _ _ <= Indirect_link s2 _ _ _ = s1 <= s2
  Direct_link _ _ <= _ = True
  Indirect_link _ _ _ _ <= _ = False

instance Eq LIB_NAME where
  ln1 == ln2 = getLIB_ID ln1 == getLIB_ID ln2

instance Ord LIB_NAME where
  ln1 <= ln2 = getLIB_ID ln1 <= getLIB_ID ln2
