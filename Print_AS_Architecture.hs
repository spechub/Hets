
{- HetCATS/Print_AS_Architecture.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   Printing the Architechture stuff of HetCASL.

   todo:
     - ATermConversion SML-CATS has now his own module 
       (s. HetCATS/aterm_conv/)
     - LaTeX Pretty Printing
-}

module Print_AS_Architecture where

import Pretty
import PrettyPrint

import AS_Architecture

import Id
import Print_AS_Annotation
import Print_AS_Structured

import Logic
import LogicGraph
import Grothendieck

instance PrettyPrint ARCH_SPEC_DEFN where
    printText0 ga (Arch_spec_defn aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'

instance PrettyPrint ARCH_SPEC where
    printText0 ga (Basic_arch_spec aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'
    printText0 ga (Arch_spec_name aa) =
	let aa' = printText0 ga aa
	in aa'
    printText0 ga (Group_arch_spec aa _) =
	let aa' = printText0 ga aa
	in aa'

instance PrettyPrint UNIT_DECL_DEFN where
    printText0 ga (Unit_decl aa ab ac _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	    ac' = printText0 ga ac
	in aa' <+> ab' <+> ac'
    printText0 ga (Unit_defn aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'

instance PrettyPrint UNIT_SPEC_DEFN where
    printText0 ga (Unit_spec_defn aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'

instance PrettyPrint UNIT_SPEC where
    printText0 ga (Unit_type aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'
    printText0 ga (Spec_name aa) =
	let aa' = printText0 ga aa
	in aa'
    printText0 ga (Arch_unit_spec aa _) =
	let aa' = printText0 ga aa
	in aa'
    printText0 ga (Closed_unit_spec aa _) =
	let aa' = printText0 ga aa
	in aa'

instance PrettyPrint UNIT_EXPRESSION where
    printText0 ga (Unit_expression aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'

instance PrettyPrint UNIT_BINDING where
    printText0 ga (Unit_binding aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'

instance PrettyPrint UNIT_TERM where
    printText0 ga (Unit_reduction aa ab) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'
    printText0 ga (Unit_translation aa ab) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'
    printText0 ga (Amalgamation aa _) =
	let aa' = printText0 ga aa
	in aa'
    printText0 ga (Local_unit aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'
    printText0 ga (Unit_appl aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'
    printText0 ga (Group_unit_term aa _) =
	let aa' = printText0 ga aa
	in aa'

instance PrettyPrint FIT_ARG_UNIT where
    printText0 ga (Fit_arg_unit aa (G_symb_map_items_list lid ab) _) =
	let aa' = printText0 ga aa
	    ab' = cat $ map (print_symb_map_items_text lid ga) ab
	in aa' <+> ab'

