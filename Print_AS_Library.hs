{- HetCATS/Print_AS_Library.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   These data structures describe the abstract syntax tree for heterogenous 
   libraries in HetCASL.

   todo:
     - ATermConversion SML-CATS has now his own module 
       (s. HetCATS/aterm_conv/)
     - LaTeX Pretty Printing
-}

module Print_AS_Library where

import Pretty
import PrettyPrint

import Id
import AS_Library

import Print_AS_Annotation
import Print_AS_Architecture
import Print_AS_Structured

import Logic
import Grothendieck

instance PrettyPrint LIB_DEFN where
    printText0 ga (Lib_defn aa ab _ ad) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	    ad' = printText0 ga ad
	in aa' <+> ab' <+> ad'

instance PrettyPrint LIB_ITEM where
    printText0 ga (Spec_defn aa ab ac _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	    ac' = printText0 ga ac
	in aa' <+> ab' <+> ac'
    printText0 ga (View_defn aa ab ac ad _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	    ac' = printText0 ga ac
	    ad' = printText0 ga ad
	in aa' <+> ab' <+> ac' <+> ad'
    printText0 ga (Arch_spec_defn aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'
    printText0 ga (Unit_spec_defn aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'
    printText0 ga (Download_items aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'
    printText0 ga (Logic aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'

instance PrettyPrint ITEM_NAME_OR_MAP where
    printText0 ga (Item_name aa) =
	let aa' = printText0 ga aa
	in aa'
    printText0 ga (Item_name_map aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'

instance PrettyPrint LIB_NAME where
    printText0 ga (Lib_version aa ab) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'
    printText0 ga (Lib_id aa) =
	let aa' = printText0 ga aa
	in aa'

instance PrettyPrint LIB_ID where
    printText0 ga (Direct_link aa _) =
	let aa' = printText0 ga aa
	in aa'
    printText0 ga (Indirect_link aa _) =
	let aa' = printText0 ga aa
	in aa'

instance PrettyPrint VERSION_NUMBER where
    printText0 ga (Version_number aa _) =
	let aa' = printText0 ga aa
	in aa'



