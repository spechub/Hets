{-| 
   
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

   LaTeX Printing the Architechture stuff of HetCASL.
-}

module Syntax.LaTeX_AS_Architecture where

import Common.Lib.Pretty
import Common.PrintLaTeX
import Common.LaTeX_utils
import Syntax.AS_Architecture
import Syntax.LaTeX_AS_Structured
import Syntax.Print_AS_Structured
import Syntax.Print_AS_Architecture
import Logic.Grothendieck

instance PrintLaTeX ARCH_SPEC where
    printLatex0 ga (Basic_arch_spec aa ab _) =
	let aa' = fsep $ punctuate semi $ map (printLatex0 ga) aa
	    ab' = printLatex0 ga ab
	in (hang (ptext "units") 4 aa') $$ (ptext "result" <+> ab')
    printLatex0 ga (Arch_spec_name aa) =
	printLatex0 ga aa
    printLatex0 ga (Group_arch_spec aa _) =
	braces $ printLatex0 ga aa

instance PrintLaTeX UNIT_DECL where
    printLatex0 ga (Unit_decl aa ab _) =
	let aa' = simple_id_latex aa
	    ab' = printLatex0 ga ab
	in aa' <> colon <+> ab'

instance PrintLaTeX UNIT_DECL_DEFN where
    printLatex0 ga (Unit_decl_defn u) = printLatex0 ga u
    printLatex0 ga (Unit_defn aa ab _) =
	let aa' = simple_id_latex aa
	    ab' = printLatex0 ga ab
	in hang (aa' <+> equals) 4 ab'

instance PrintLaTeX UNIT_SPEC where
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
    printLatex0 ga (Closed_unit_spec aa _) =
	let aa' = printLatex0 ga aa
	in hang (ptext "closed") 4 aa'

instance PrintLaTeX REF_SPEC where
    printLatex0 ga (Unit_spec u) = printLatex0 ga u
    printLatex0 ga (Arch_unit_spec aa _) =
	let aa' = printLatex0 ga aa
	in hang (ptext "arch spec") 4 aa'

instance PrintLaTeX UNIT_EXPRESSION where
    printLatex0 ga (Unit_expression aa ab _) =
	let aa' = cat $ punctuate (semi <> space) $ map (printLatex0 ga) aa
	    ab' = printLatex0 ga ab
	in if null aa then ab' 
	   else hang (ptext "lambda") 4 (hang aa' (-2) (ptext "." <+> ab'))

instance PrintLaTeX UNIT_BINDING where
    printLatex0 ga (Unit_binding aa ab _) =
	let aa' = printLatex0 ga aa
	    ab' = printLatex0 ga ab
	in aa' <+> colon <+> ab'

instance PrintLaTeX UNIT_TERM where
    printLatex0 ga (Unit_reduction aa ab) =
	let aa' = printLatex0 ga aa
	    ab' = printLatex0 ga ab
	in fsep [aa', ab']
    printLatex0 ga (Unit_translation aa ab) =
	let aa' = printLatex0 ga aa
	    ab' = printLatex0 ga ab
	in fsep [aa', ab']
    printLatex0 ga (Amalgamation aa _) =
	fsep $ punctuate (space <> ptext "and") $ map (printLatex0 ga) aa
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
	sp_between_latex (latex_macro "\\{") (latex_macro "\\}") 
			     $ printLatex0 ga aa

instance PrintLaTeX FIT_ARG_UNIT where
    printLatex0 ga (Fit_arg_unit aa ab _) =
	printLatex0 ga aa <> 
        (if null ab then empty else space <> 
            hc_sty_plain_keyword "fit"<\+>
            set_tabbed_nest_latex (fsep_latex (map (printLatex0 ga) ab)))


