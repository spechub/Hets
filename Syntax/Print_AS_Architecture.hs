{-| 
   
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

   Printing the Architechture stuff of HetCASL.
-}
{-
   todo:
     - ATermConversion SML-CATS has now his own module 
       (s. HetCATS/aterm_conv/)
     - LaTeX Pretty Printing
-}

module Syntax.Print_AS_Architecture where

import Common.Lib.Pretty
import Common.PrettyPrint
import Common.PPUtils

import Syntax.AS_Architecture

import Syntax.Print_AS_Structured


import Data.List

import Logic.Grothendieck

instance PrettyPrint ARCH_SPEC where
    printText0 ga (Basic_arch_spec aa ab _) =
	let aa' = fsep $ punctuate semi $ map (printText0 ga) aa
	    ab' = printText0 ga ab
	in (hang (ptext "units") 4 aa') $$ (ptext "result" <+> ab')
    printText0 ga (Arch_spec_name aa) =
	printText0 ga aa
    printText0 ga (Group_arch_spec aa _) =
	braces $ printText0 ga aa

    printLatex0 ga (Basic_arch_spec aa ab _) =
	let aa' = fsep $ punctuate semi $ map (printLatex0 ga) aa
	    ab' = printLatex0 ga ab
	in (hang (ptext "units") 4 aa') $$ (ptext "result" <+> ab')
    printLatex0 ga (Arch_spec_name aa) =
	printLatex0 ga aa
    printLatex0 ga (Group_arch_spec aa _) =
	braces $ printLatex0 ga aa

instance PrettyPrint UNIT_DECL_DEFN where
    printText0 ga (Unit_decl aa ab ac _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	    ac' = if null ac then empty 
	          else ptext "given" <+> 
		       (fcat $  punctuate (comma <> space) $ 
			           map (printText0 ga) ac)
	in hang (aa' <> colon <+> ab') 4  ac'
    printText0 ga (Unit_defn aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in hang (aa' <+> equals) 4 ab'

    printLatex0 ga (Unit_decl aa ab ac _) =
	let aa' = simple_id_latex aa
	    ab' = printLatex0 ga ab
	    ac' = if null ac then empty 
	          else ptext "given" <+> 
		       (fcat $  punctuate (comma <> space) $ 
			           map (printLatex0 ga) ac)
	in hang (aa' <> colon <+> ab') 4  ac'
    printLatex0 ga (Unit_defn aa ab _) =
	let aa' = simple_id_latex aa
	    ab' = printLatex0 ga ab
	in hang (aa' <+> equals) 4 ab'

instance PrettyPrint UNIT_SPEC where
    printText0 ga (Unit_type aa ab _) =
	let aa' = fsep $ punctuate (ptext " * ") $ 
			 map (condBracesGroupSpec printText0 
			                   braces Nothing ga) aa
	    ab' = printText0 ga ab
	in if null aa then ab' else aa' <+> ptext "->" <+> ab'
    printText0 ga (Spec_name aa) =
	let aa' = printText0 ga aa
	in aa'
    printText0 ga (Arch_unit_spec aa _) =
	let aa' = printText0 ga aa
	in hang (ptext "arch spec") 4 aa'
    printText0 ga (Closed_unit_spec aa _) =
	let aa' = printText0 ga aa
	in hang (ptext "closed") 4 aa'

    printLatex0 ga (Unit_type aa ab _) =
	let aa' = fsep $ punctuate (ptext " * ") $ 
			 map (condBracesGroupSpec printLatex0 
			         braces_latex Nothing ga) 
			     aa
	    ab' = printLatex0 ga ab
	in if null aa then ab' else aa' <+> ptext "->" <+> ab'
    printLatex0 ga (Spec_name aa) =
	let aa' = printLatex0 ga aa
	in aa'
    printLatex0 ga (Arch_unit_spec aa _) =
	let aa' = printLatex0 ga aa
	in hang (ptext "arch spec") 4 aa'
    printLatex0 ga (Closed_unit_spec aa _) =
	let aa' = printLatex0 ga aa
	in hang (ptext "closed") 4 aa'

instance PrettyPrint UNIT_EXPRESSION where
    printText0 ga (Unit_expression aa ab _) =
	let aa' = cat $ punctuate (semi <> space) $ map (printText0 ga) aa
	    ab' = printText0 ga ab
	in if null aa then ab' 
	   else hang (ptext "lambda") 4 (hang aa' (-2) (ptext "." <+> ab'))

    printLatex0 ga (Unit_expression aa ab _) =
	let aa' = cat $ punctuate (semi <> space) $ map (printLatex0 ga) aa
	    ab' = printLatex0 ga ab
	in if null aa then ab' 
	   else hang (ptext "lambda") 4 (hang aa' (-2) (ptext "." <+> ab'))

instance PrettyPrint UNIT_BINDING where
    printText0 ga (Unit_binding aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> colon <+> ab'

    printLatex0 ga (Unit_binding aa ab _) =
	let aa' = printLatex0 ga aa
	    ab' = printLatex0 ga ab
	in aa' <+> colon <+> ab'

instance PrettyPrint UNIT_TERM where
    printText0 ga (Unit_reduction aa ab) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in fsep [aa', ab']
    printText0 ga (Unit_translation aa ab) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in fsep [aa', ab']
    printText0 ga (Amalgamation aa _) =
	fsep $ intersperse (ptext "and") $ map (printText0 ga) aa
    printText0 ga (Local_unit aa ab _) =
	let aa' = fcat $ punctuate (semi<>space) $ map (printText0 ga) aa
	    ab' = printText0 ga ab
	in (hang (ptext "local") 4 aa') $$ 
	   (hang (ptext "within") 4 ab')
    printText0 ga (Unit_appl aa ab _) =
	let aa' = printText0 ga aa
	    ab' = fsep $ map (brackets . (printText0 ga)) ab
	in aa' <+> (if null ab then empty else ab')
    printText0 ga (Group_unit_term aa _) =
	braces $ printText0 ga aa

    printLatex0 ga (Unit_reduction aa ab) =
	let aa' = printLatex0 ga aa
	    ab' = printLatex0 ga ab
	in fsep [aa', ab']
    printLatex0 ga (Unit_translation aa ab) =
	let aa' = printLatex0 ga aa
	    ab' = printLatex0 ga ab
	in fsep [aa', ab']
    printLatex0 ga (Amalgamation aa _) =
	fsep $ intersperse (ptext "and") $ map (printLatex0 ga) aa
    printLatex0 ga (Local_unit aa ab _) =
	let aa' = fcat $ punctuate (semi<>space) $ map (printLatex0 ga) aa
	    ab' = printLatex0 ga ab
	in (hang (ptext "local") 4 aa') $$ 
	   (hang (ptext "within") 4 ab')
    printLatex0 ga (Unit_appl aa ab _) =
	let aa' = simple_id_latex aa
	    ab' = fsep $ map (brackets . (printLatex0 ga)) ab
	in aa' <+> (if null ab then empty else ab')
    printLatex0 ga (Group_unit_term aa _) =
	sp_between (latex_macro "\\{") (latex_macro "\\}") $ printLatex0 ga aa

instance PrettyPrint FIT_ARG_UNIT where
    printText0 ga (Fit_arg_unit aa ab _) =
	let aa' = printText0 ga aa
	  --  ab' = fcat $ punctuate (comma<>space) $ 
	  --                 map (print_symb_map_items_text lid ga) ab
	    ab' = printText0 ga ab
	    null' = case ab of
	            G_symb_map_items_list _ l -> null l
	in aa' <+> (if null' then empty else ptext "fit" <+> ab')

    printLatex0 ga (Fit_arg_unit aa ab _) =
	let aa' = printLatex0 ga aa
	    ab' = printLatex0 ga ab
	    null' = case ab of
	            G_symb_map_items_list _ l -> null l
	in aa' <+> (if null' then empty else ptext "fit" <+> ab')

