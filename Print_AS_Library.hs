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

-- debugging
-- import IOExts (trace)
import Pretty
import PrettyPrint

import Id
import qualified AS_Structured as AS_Struct 
import AS_Library

import Print_AS_Annotation
import Print_AS_Architecture
import Print_AS_Structured

instance PrettyPrint LIB_DEFN where
    printText0 ga (Lib_defn aa ab _ ad) =
	let aa' = printText0 ga aa
	    pt x = printText0 ga x  
	    ab' = vcat $ map pt ab
	    ad' = printText0 ga ad
	in ptext "library" <+> aa' $$ ad' $$ ptext "\n" $$ ab'

instance PrettyPrint LIB_ITEM where
    printText0 ga (Spec_defn aa ab ac _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	    ac' = printText0 ga ac
         -- nesting is done by the instance for SPEC now
	in (ptext "spec" <+> aa' <+> ab' <+> equals) $$ ac' $$ ptext "end\n"
	   
    printText0 ga (View_defn aa ab ac ad _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	    ac' = printText0 ga ac
	    ad' = fcat $ punctuate (comma<>space) $ map (printText0 ga) ad
	    eq' = if null ad then empty else equals
	in (hang (ptext "view" <+> aa' <+> ab' <+> colon <+> ac' <+> eq') 4 
	         ad') $$ ptext "end\n"
{-
data VIEW_DEFN = View_defn VIEW_NAME GENERICITY VIEW_TYPE
			   [G_mapping] [Pos]

-}
    printText0 ga (Arch_spec_defn aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in (hang (ptext "arch spec" <+> aa' <+> equals) 4 ab') $$ ptext "end\n"
    printText0 ga (Unit_spec_defn aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in (hang (ptext "unit spec" <+> aa' <+> equals) 4 ab') $$ ptext "end\n"
    printText0 ga (Download_items aa ab _) =
	let aa' = printText0 ga aa
	    ab' = fcat $ punctuate (comma<>space) $ map (printText0 ga) ab
	in (hang (ptext "from" <+> aa' <+> ptext "get") 4 ab') $$ 
	   ptext "end\n" 
    printText0 ga (AS_Library.Logic aa _) =
	let aa' = printText0 ga aa
	in ptext "logic" <+> aa' 

instance PrettyPrint ITEM_NAME_OR_MAP where
    printText0 ga (Item_name aa) =
	let aa' = printText0 ga aa
	in aa'
    printText0 ga (Item_name_map aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ptext "|->" <+> ab'

instance PrettyPrint LIB_NAME where
    printText0 ga (Lib_version aa ab) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ptext "version" <+> ab'
    printText0 ga (Lib_id aa) =
	printText0 ga aa

instance PrettyPrint LIB_ID where
    printText0 ga (Direct_link aa _) =
	printText0 ga aa
    printText0 ga (Indirect_link aa _) =
	printText0 ga aa


instance PrettyPrint VERSION_NUMBER where
    printText0 ga (Version_number aa _) =
	hcat $ punctuate (char '.') $ map (printText0 ga) aa

