{-| 
   
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

   These data structures describe the abstract syntax tree for heterogenous 
   libraries in HetCASL.
-}

{-
   todo:
     - ATermConversion SML-CATS has now his own module 
       (s. HetCATS/aterm_conv/)
     - LaTeX Pretty Printing
-}

module Syntax.Print_AS_Library where

-- debugging
-- import IOExts (trace)

import Common.Lib.Pretty
import Common.PrettyPrint
import Common.PPUtils
import Common.GlobalAnnotations

import Common.Id
import qualified Syntax.AS_Structured as AS_Struct 
import Syntax.AS_Library
import Common.AS_Annotation

import Common.Print_AS_Annotation
import Syntax.Print_AS_Architecture
import Syntax.Print_AS_Structured

instance PrettyPrint LIB_DEFN where
    printText0 ga (Lib_defn aa ab _ ad) =
	let aa' = printText0 ga aa              -- lib name
	    ab' = vcat $ map (printText0 ga) ab -- LIB_ITEMs
	    ad' = vcat $ map (printText0 ga) ad -- global ANNOTATIONs
	in ptext "library" <+> aa' <> ptext "\n" $$ ad' $$ ptext "\n" $$ ab'

instance PrettyPrint LIB_ITEM where
    printText0 ga (Spec_defn aa ab ac _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	    spec_head = ptext "spec" <+> aa' <+> ab' <+> equals
	    ac' = spAnnotedPrint (printText0 ga) (printText0 ga) (<+>) 
		  (spec_head) ac
         -- nesting is done by the instance for SPEC now
	in ac' $$ ptext "end\n"
	   
    printText0 ga (View_defn aa ab ac ad _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	    -- ac' = printText0 ga ac
	    (frm,to) = case ac of 
		       AS_Struct.View_type vaa vab _ -> 
			   (condBracesGroupSpec printText0 braces 
			        Nothing ga vaa, 
			    condBracesGroupSpec printText0 braces 
			        Nothing ga vab)
	    ad' = sep $ punctuate comma $ map (printText0 ga) ad
	    eq' = if null ad then empty else equals
	in (hang (hang (hang (hang (ptext "view" <+> aa' <+> ab') 
			           6 
			           (colon <+> frm <+> ptext "to")) 
			     4 
                             to) 
		       2 
		       eq') 
	         4 
	         ad') 
	   $$ ptext "end\n"
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
	    ab' = fsep $ punctuate comma $ map (printText0 ga) ab
	in (hang (ptext "from" <+> aa' <+> ptext "get") 4 ab') <> ptext "\n"
    printText0 ga (Syntax.AS_Library.Logic_decl aa _) =
	let aa' = printText0 ga aa
	in ptext "logic" <+> aa' 

condBracesGroupSpec4View_defn :: 
    (GlobalAnnos -> (Annoted AS_Struct.SPEC) -> Doc)
	-> (Doc -> Doc) -- ^ a function enclosing the Doc
                        -- in braces
	-> GlobalAnnos -> (Annoted AS_Struct.SPEC) -> Doc
condBracesGroupSpec4View_defn pf b_fun ga as =
    case skip_Group $ item as of
		 AS_Struct.Spec_inst _ _ _ -> as'
		 AS_Struct.Union _ _       -> nested'
		 AS_Struct.Extension _ _   -> nested'
		 _                         -> nested'

    where nested' = b_fun as' 
          as' = pf ga as

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
    printText0 _ (Direct_link aa _) =
	ptext aa
    printText0 _ (Indirect_link aa _) =
	ptext aa

instance PrettyPrint VERSION_NUMBER where
    printText0 _ (Version_number aa _) =
	hcat $ punctuate (char '.') $ map ptext aa
