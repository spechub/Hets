{-| 
   
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

   These data structures describe the abstract syntax tree for heterogenous 
   libraries in HetCASL.
   Follows Sect. II:2.2.5 of the CASL Reference Manual.

-}
{-
   todo:
     - ATermConversion SML-CATS has now his own module 
       (s. HetCATS/aterm_conv/)
     - LaTeX Pretty Printing
-}

module Syntax.AS_Library where

-- DrIFT command:
{-! global: UpPos !-}

import Common.Id
import Common.AS_Annotation

import qualified Syntax.AS_Architecture
import qualified Syntax.AS_Structured


data LIB_DEFN = Lib_defn LIB_NAME [Annoted LIB_ITEM] [Pos] [Annotation]
	        -- pos: "library"
	        -- list of annotations is parsed preceding the first LIB_ITEM
	        -- the last LIB_ITEM may be annotated with a following comment
	        -- the first LIB_ITEM cannot be annotated
		deriving (Show)

{- for information on the list of Pos see the documentation in
   AS_Structured.hs and AS_Architecture.hs -}

data LIB_ITEM = Spec_defn Syntax.AS_Structured.SPEC_NAME 
		          Syntax.AS_Structured.GENERICITY 
                          (Annoted Syntax.AS_Structured.SPEC) 
			  [Pos]
	      
	      | View_defn Syntax.AS_Structured.VIEW_NAME 
		          Syntax.AS_Structured.GENERICITY 
			  Syntax.AS_Structured.VIEW_TYPE 
			  [Syntax.AS_Structured.G_mapping]
			  [Pos]

	      | Arch_spec_defn Syntax.AS_Architecture.ARCH_SPEC_NAME 
		               (Annoted Syntax.AS_Architecture.ARCH_SPEC) 
			       [Pos]

	      | Unit_spec_defn Syntax.AS_Structured.SPEC_NAME 
		               Syntax.AS_Architecture.UNIT_SPEC 
			       [Pos]

	      | Ref_spec_defn Syntax.AS_Structured.SPEC_NAME 
		               Syntax.AS_Architecture.REF_SPEC 
			       [Pos]

	      | Download_items  LIB_NAME [ITEM_NAME_OR_MAP] [Pos] 
		-- pos: "from","get",commas, opt "end"
	      | Logic_decl Syntax.AS_Structured.Logic_name [Pos]
		-- pos:  "logic", Logic_name
		deriving (Show)

data ITEM_NAME_OR_MAP = Item_name ITEM_NAME 
		      | Item_name_map ITEM_NAME ITEM_NAME [Pos]
			-- pos: "|->"
			deriving (Show,Eq)

type ITEM_NAME = SIMPLE_ID

data LIB_NAME = Lib_version LIB_ID VERSION_NUMBER
	      | Lib_id LIB_ID

data LIB_ID = Direct_link URL [Pos]
	      -- pos: start of URL
	    | Indirect_link PATH [Pos]
	      -- pos: start of PATH



data VERSION_NUMBER = Version_number [String] [Pos]
		      -- pos: "version", start of first string
		      deriving (Show,Eq) 

type URL = String
type PATH = String


instance Show LIB_ID where
  show (Direct_link s1 _) = s1
  show (Indirect_link s1 _) = s1

instance Show LIB_NAME where
  show (Lib_version libid _) = show libid
  show (Lib_id libid) = show libid

instance Eq LIB_ID where
  Direct_link s1 _ == Direct_link s2 _ = s1==s2
  Indirect_link s1 _ == Indirect_link s2 _ = s1==s2
  _ == _ = False

instance Ord LIB_ID where
  Direct_link s1 _ <= Direct_link s2 _ = s1<=s2
  Indirect_link s1 _ <= Indirect_link s2 _ = s1<=s2
  Direct_link _ _ <= _ = True
  Indirect_link _ _ <= _ = False

getLIB_ID :: LIB_NAME -> LIB_ID
getLIB_ID (Lib_version libid _) = libid
getLIB_ID (Lib_id libid) = libid

instance Eq LIB_NAME where
  ln1 == ln2 = getLIB_ID ln1 == getLIB_ID ln2
  
instance Ord LIB_NAME where
  ln1 <= ln2 = getLIB_ID ln1 <= getLIB_ID ln2

-- functions for casts
cast_S_L_Spec_defn :: Syntax.AS_Structured.SPEC_DEFN -> LIB_ITEM 
cast_L_S_Spec_defn :: LIB_ITEM  -> Syntax.AS_Structured.SPEC_DEFN

cast_S_L_Spec_defn (Syntax.AS_Structured.Spec_defn x y z p) = 
    (Syntax.AS_Library.Spec_defn x y z p) 
cast_S_L_Spec_defn _ = error "wrong constructor for \"cast_S_L_Spec_defn\""

cast_L_S_Spec_defn (Syntax.AS_Library.Spec_defn x y z p) =
    (Syntax.AS_Structured.Spec_defn x y z p)
cast_L_S_Spec_defn _ = error "wrong constructor for \"cast_L_S_Spec_defn\""

cast_S_L_View_defn :: Syntax.AS_Structured.VIEW_DEFN -> LIB_ITEM 
cast_L_S_View_defn :: LIB_ITEM  -> Syntax.AS_Structured.VIEW_DEFN

cast_S_L_View_defn (Syntax.AS_Structured.View_defn w x y z p) = 
    (Syntax.AS_Library.View_defn w x y z p) 
cast_S_L_View_defn _ = error "wrong constructor for \"cast_S_L_View_defn\""

cast_L_S_View_defn (Syntax.AS_Library.View_defn w x y z p) =
    (Syntax.AS_Structured.View_defn w x y z p)
cast_L_S_View_defn _ = error "wrong constructor for \"cast_L_S_View_defn\""

cast_A_L_Arch_spec_defn :: Syntax.AS_Architecture.ARCH_SPEC_DEFN -> LIB_ITEM
cast_L_A_Arch_spec_defn :: LIB_ITEM       -> Syntax.AS_Architecture.ARCH_SPEC_DEFN

cast_A_L_Arch_spec_defn (Syntax.AS_Architecture.Arch_spec_defn x y p) =
    (Syntax.AS_Library.Arch_spec_defn x y p)
cast_A_L_Arch_spec_defn _ = 
    error "wrong constructor for \"cast_A_L_Arch_defn\""

cast_L_A_Arch_spec_defn (Syntax.AS_Library.Arch_spec_defn x y p) =
    (Syntax.AS_Architecture.Arch_spec_defn x y p)
cast_L_A_Arch_defn _ = error "wrong constructor for \"cast_L_A_Arch_defn\""

cast_A_L_Unit_spec_defn :: Syntax.AS_Architecture.UNIT_SPEC_DEFN -> LIB_ITEM
cast_L_A_Unit_spec_defn :: LIB_ITEM       -> Syntax.AS_Architecture.UNIT_SPEC_DEFN

cast_A_L_Unit_spec_defn (Syntax.AS_Architecture.Unit_spec_defn x y p) =
    (Syntax.AS_Library.Unit_spec_defn x y p)
cast_A_L_Unit_defn _ = error "wrong constructor for \"cast_A_L_Unit_defn\""

cast_L_A_Unit_spec_defn (Syntax.AS_Library.Unit_spec_defn x y p) =
    (Syntax.AS_Architecture.Unit_spec_defn x y p)
cast_L_A_Spec_defn _ = error "wrong constructor for \"cast_L_A_Unit_defn\""
