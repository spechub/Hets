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
import PPUtils

import Id
import qualified AS_Structured as AS_Struct 
import AS_Library

import Print_AS_Annotation
import Print_AS_Architecture
import Print_AS_Structured

instance PrettyPrint LIB_DEFN where
    printText0 ga (Lib_defn aa ab _ ad) =
	let aa' = printText0 ga aa              -- lib name
	    ab' = vcat $ map (printText0 ga) ab -- LIB_ITEMs
	    ad' = printText0 ga ad              -- global ANNOTATIONs
	in ptext "library" <+> aa' $$ ad' $$ ptext "\n" $$ ab'

    printLatex0 ga (Lib_defn aa ab _ ad) =
	let aa' = printLatex0 ga aa              -- lib name
	    ab' = vcat $ map (printLatex0 ga) ab -- LIB_ITEMs
	    ad' = printLatex0 ga ad              -- global ANNOTATIONs
	in hc_sty_plain_keyword "library" <\+> aa' $$ ad' 
	       $$ latex_macro "\n" $$ ab'

instance PrettyPrint LIB_ITEM where
    printText0 ga (Spec_defn aa ab ac _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	    spec_head = (hang (ptext "spec" <+> aa' <+> ab') 2 equals)
	    ac' = spAnnotedPrint printText0 (<+>) ga (spec_head) ac
         -- nesting is done by the instance for SPEC now
	in ac' $$ ptext "end\n"
	   
    printText0 ga (View_defn aa ab ac ad _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	    -- ac' = printText0 ga ac
	    (frm,to) = case ac of 
		       AS_Struct.View_type vaa vab _ -> 
			   (condBracesGroupSpec printText0 sp_braces ga vaa, 
			    condBracesGroupSpec printText0 sp_braces ga vab)
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
	in (hang (ptext "from" <+> aa' <+> ptext "get") 4 ab') <+> ptext "\n"
    printText0 ga (AS_Library.Logic aa _) =
	let aa' = printText0 ga aa
	in ptext "logic" <+> aa' 

    printLatex0 ga (Spec_defn aa ab ac _) =
	let aa' = simple_id_latex aa
	    ab' = printLatex0 ga ab
	    spec_head = (hang_latex (hc_sty_hetcasl_keyword "spec" 
				         <\+> aa' <\+> ab') 
			     2 equals_latex)
	    ac' = spAnnotedPrint printLatex0 (<\+>) ga (spec_head) ac
	in ac' $$ latexEnd 
    printLatex0 ga (View_defn aa ab ac ad _) =
	let aa' = simple_id_latex aa
	    ab' = printLatex0 ga ab
	    condGrpSp = condBracesGroupSpec printLatex0 sp_braces_latex ga
	    (frm,to) = case ac of 
		       AS_Struct.View_type vaa vab _ -> 
			    (condGrpSp vaa, condGrpSp vab)
	    ad' = cat $ punctuate (comma_latex<>space_latex) $ 
	                 map (printLatex0 ga) ad
	    eq' = if null ad then empty else equals_latex
	in (hang_latex 
	        (hang_latex 
		     (hang_latex 
		          (hang_latex 
			       (hc_sty_hetcasl_keyword "view" 
				<\+> aa' <\+> ab') 
			       6 
			       (colon_latex 
				<\+> frm 
				<\+> hc_sty_plain_keyword "to")) 
		          4 
                          to) 
		     2 
		     eq') 
	        4 
	        ad') 
	    $$ latexEnd
    printLatex0 ga (Arch_spec_defn aa ab _) =
	let aa' = simple_id_latex aa
	    ab' = printLatex0 ga ab
	in (hang_latex 
	        (hc_sty_plain_keyword "arch spec" <\+> aa' 
		 <\+> equals_latex) 
	        4 ab') 
           $$ latexEnd
    printLatex0 ga (Unit_spec_defn aa ab _) =
	let aa' = hc_sty_id $ tokStr aa
	    ab' = printLatex0 ga ab
	in (hang_latex (hc_sty_plain_keyword "unit spec" <\+> aa' 
			<\+> equals_latex) 
	               4 ab') 
	   $$ latexEnd
    printLatex0 ga (Download_items aa ab _) =
	let aa' = printLatex0 ga aa
	    ab' = fsep_latex $ punctuate comma_latex $ 
	                       map (printLatex0 ga) ab
	in (hc_sty_hetcasl_keyword "from" <\+> aa' 
			<\+> hc_sty_plain_keyword "get") 
	   $$ hetcasl_nest_latex ab' <> latex_macro "\n"
    printLatex0 ga (AS_Library.Logic aa _) =
	let aa' = printLatex0 ga aa
	in hc_sty_plain_keyword "logic" <\+> aa' 

instance PrettyPrint ITEM_NAME_OR_MAP where
    printText0 ga (Item_name aa) =
	let aa' = printText0 ga aa
	in aa'
    printText0 ga (Item_name_map aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ptext "|->" <+> ab'

    printLatex0 _ga (Item_name aa) =
	simple_id_latex aa
    printLatex0 _ga (Item_name_map aa ab _) =
	simple_id_latex aa <\+> hc_sty_axiom "\\mapsto" <\+> simple_id_latex ab

instance PrettyPrint LIB_NAME where
    printText0 ga (Lib_version aa ab) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ptext "version" <+> ab'
    printText0 ga (Lib_id aa) =
	printText0 ga aa

    printLatex0 ga (Lib_version aa ab) =
	let aa' = printLatex0 ga aa
	    ab' = printLatex0 ga ab
	in aa' <\+> hc_sty_plain_keyword "version" <\+> ab'
    printLatex0 ga (Lib_id aa) = printLatex0 ga aa

instance PrettyPrint LIB_ID where
    printText0 _ (Direct_link aa _) =
	ptext aa
    printText0 _ (Indirect_link aa _) =
	ptext aa

    printLatex0 _ (Direct_link aa _) =
	hc_sty_structid aa
    printLatex0 _ (Indirect_link aa _) =
	hc_sty_structid aa

instance PrettyPrint VERSION_NUMBER where
    printText0 ga (Version_number aa _) =
	hcat $ punctuate (char '.') $ map (printText0 ga) aa
    printLatex0 _ (Version_number aa _) =
	hcat $ punctuate (casl_normal_latex ".") $ map casl_normal_latex aa

latexEnd :: Doc
latexEnd = hc_sty_plain_keyword "end" <> latex_macro "\n"
