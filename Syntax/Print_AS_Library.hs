{- HetCATS/Syntax/Print_AS_Library.hs
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

    printLatex0 ga (Lib_defn aa ab _ ad) =
	let aa' = printLatex0 ga' aa              -- lib name
	    ab' = vcat $ map (printLatex0 ga') ab -- LIB_ITEMs
	    ad' = vcat $ map (printLatex0 ga') ad -- global ANNOTATIONs
	    ga' = set_latex_print True ga
	in hc_sty_plain_keyword "library" <\+> aa' 
	       <> latex_macro "\n" $$ ad' 
	       $$ latex_macro "\n" $$ ab'

instance PrettyPrint LIB_ITEM where
    printText0 ga (Spec_defn aa ab ac _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	    spec_head = ptext "spec" <+> aa' <+> ab' <+> equals
	    ac' = spAnnotedPrint printText0 (<+>) ga (spec_head) ac
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



    printLatex0 ga (Spec_defn aa ab ac _) =
	let aa' = simple_id_indexed_latex aa
	    ab' = printLatex0 ga ab -- only PARAMS are nested/hang after 
				    -- the spec name
	    spec_head = hc_sty_hetcasl_keyword "spec" 
			<\+> setTab_latex <> aa' <\+> ab' <\+> equals_latex
	    ac' = spAnnotedPrint printLatex0 (<\+>) ga (spec_head) ac
	in ac' $$ latexEnd 
    printLatex0 ga (View_defn aa ab ac ad _) =
	let aa' = simple_id_latex aa
	    ab' = case printLatex0 ga ab of
		  ab_d 
		      | isEmpty ab_d -> empty
		      | otherwise    -> ab_d
	    condGrpSp = condBracesGroupSpec4View_defn
			     printLatex0 
			     sp_braces_latex2 ga
	    (frm,to) = case ac of 
		       AS_Struct.View_type vaa vab _ -> 
			    (condGrpSp vaa, 
			     condGrpSp vab)
	    ad' = fcat $ punctuate (comma_latex<>space_latex) $ 
	                 map (printLatex0 ga) ad
	    eq' = if null ad then empty else equals_latex
	    vhead = hc_sty_hetcasl_keyword "view" <\+> 
		   setTab_latex <> aa' <\+> ab' 
	    to' = if isEmpty eq' then to else to <\+> eq'
	    head_with_type = 
		fsep [vhead <\+> colon_latex, 
		      fsep [frm <\+> hc_sty_plain_keyword "to",
		      to']]	                  
	    in (if isEmpty eq' 
		then head_with_type
		else head_with_type $$ tabbed_nest_latex ad'
	       ) 
		   $$ latexEnd


{- (hang_latex 
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
		-}

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
	in (hang_latex (hc_sty_hetcasl_keyword "from" <\+> setTab_latex <>aa' 
			<\+> hc_sty_plain_keyword "get") 
	               8 
	               (tabbed_nest_latex ab')) <> latex_macro "\n"
    printLatex0 ga (Syntax.AS_Library.Logic_decl aa _) =
	let aa' = printLatex0 ga aa
	in hc_sty_plain_keyword "logic" <\+> aa' 

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
		 _                         -> tabbed_nest_latex 
					         $ b_fun 
						   (set_tabbed_nest_latex as')
    where nested' =  tabbed_nest_latex
		      (format_line <>
		           b_fun (set_tabbed_nest_latex 
				     (latex_macro "\\>"<>as')))
          as' = pf ga as
	  format_line = latex_macro "\\{\\=\\KW{view}~\\=\\kill\n"	

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
    printText0 _ (Version_number aa _) =
	hcat $ punctuate (char '.') $ map ptext aa
    printLatex0 _ (Version_number aa _) =
	hcat $ punctuate (casl_normal_latex ".") $ map casl_normal_latex aa

latexEnd :: Doc
latexEnd = hc_sty_plain_keyword "end" <> latex_macro "\n"
