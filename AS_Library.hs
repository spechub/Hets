{- HetCATS/AS_Library.hs
   $Id$
   Klaus Luettich

   These data structures describe the abstract syntax tree for heterogenous 
   libraries in HetCASL.

   todo:
-}

module AS_Library where
import AS_Architecture
import AS_Structured
import Grothendieck
import Id

data LIB_DEFN = Lib_defn(LIB_NAME,[LIB_ITEM])
		deriving (Show,Eq)

data LIB_ITEM = Spec_defn(SPEC_NAME,GENERICITY,SPEC)
--	      | SPEC_DEFN SPEC_DEFN
--	      | VIEW_DEFN
	      | View_defn(VIEW_NAME,GENERICITY,VIEW_TYPE,G_symb_map_items_list)
--	      | ARCH_SPEC_DEFN ARCH_SPEC_DEFN
	      | Arch_spec_defn(ARCH_SPEC_NAME,ARCH_SPEC)
--	      | UNIT_SPEC_DEFN UNIT_SPEC_DEFN
	      | Unit_spec_defn(SPEC_NAME,UNIT_SPEC)
--	      | DOWNLOAD_ITEMS DOWNLOAD_ITEMS
	      | Download_items (LIB_NAME,[ITEM_NAME_OR_MAP])
		deriving (Show,Eq)

data ITEM_NAME_OR_MAP = Item_name ITEM_NAME 
		      | Item_name_map(ITEM_NAME,ITEM_NAME)
			deriving (Show,Eq)

type ITEM_NAME = SIMPLE_ID

data LIB_NAME = Lib_version(LIB_ID,VERSION_NUMBER)
	      | Lib_id LIB_ID
		deriving (Show,Eq)

data LIB_ID = Direct_link URL
	    | Indirect_link PATH 
	      deriving (Show,Eq)

data VERSION_NUMBER = Version_number [Int] deriving (Show,Eq)

type URL = String
type PATH = String

-- functions for casts
cast_S_L_Spec_defn :: SPEC_DEFN -> LIB_ITEM 
cast_L_S_Spec_defn :: LIB_ITEM  -> SPEC_DEFN

cast_S_L_Spec_defn (AS_Structured.Spec_defn (x,y,z)) = 
    (AS_Library.Spec_defn (x,y,z)) 

cast_L_S_Spec_defn (AS_Library.Spec_defn (x,y,z)) =
    (AS_Structured.Spec_defn (x,y,z))

cast_S_L_View_defn :: VIEW_DEFN -> LIB_ITEM 
cast_L_S_View_defn :: LIB_ITEM  -> VIEW_DEFN

cast_S_L_View_defn (AS_Structured.View_defn (w,x,y,z)) = 
    (AS_Library.View_defn (w,x,y,z)) 

cast_L_S_View_defn (AS_Library.View_defn (w,x,y,z)) =
    (AS_Structured.View_defn (w,x,y,z))

cast_A_L_Arch_spec_defn :: ARCH_SPEC_DEFN -> LIB_ITEM
cast_L_A_Arch_spec_defn :: LIB_ITEM       -> ARCH_SPEC_DEFN

cast_A_L_Arch_spec_defn (AS_Architecture.Arch_spec_defn (x,y)) =
    (AS_Library.Arch_spec_defn (x,y))

cast_L_A_Arch_spec_defn (AS_Library.Arch_spec_defn (x,y)) =
    (AS_Architecture.Arch_spec_defn (x,y))

cast_A_L_Unit_spec_defn :: UNIT_SPEC_DEFN -> LIB_ITEM
cast_L_A_Unit_spec_defn :: LIB_ITEM       -> UNIT_SPEC_DEFN

cast_A_L_Unit_spec_defn (AS_Architecture.Unit_spec_defn (x,y)) =
    (AS_Library.Unit_spec_defn (x,y))

cast_L_A_Unit_spec_defn (AS_Library.Unit_spec_defn (x,y)) =
    (AS_Architecture.Unit_spec_defn (x,y))

