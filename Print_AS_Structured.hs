-- needs ghc -fglasgow-exts

{- HetCATS/Print_AS_Structured.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   Printing the Structured part of hetrogenous specifications.

   todo:
     - ATermConversion SML-CATS has now his own module 
       (s. HetCATS/aterm_conv/)
     - LaTeX Pretty Printing
-}

module Print_AS_Structured where

import Pretty
import PrettyPrint

-- debugging stuff
-- import IOExts (trace)

import Logic
import LogicGraph
import Grothendieck

import AS_Structured
import Print_AS_Annotation

instance PrettyPrint SPEC where
    printText0 ga (Basic_spec aa) =
	let aa' = printText0 ga aa
	in aa'
    printText0 ga (Translation aa ab) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'
    printText0 ga (Reduction aa ab) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'
    printText0 ga (Union aa _) =
	let aa' = printText0 ga aa
	in aa'
    printText0 ga (Extension aa _) =
	let aa' = printText0 ga aa
	in aa'
    printText0 ga (Free_spec aa _) =
	let aa' = printText0 ga aa
	in aa'
    printText0 ga (Local_spec aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'
    printText0 ga (Closed_spec aa _) =
	let aa' = printText0 ga aa
	in aa'
    printText0 ga (Group aa _) =
	let aa' = printText0 ga aa
	in aa'
    printText0 ga (Spec_inst aa ab) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'

instance PrettyPrint RENAMING where
    printText0 ga (Renaming aa _) =
	let aa' = printText0 ga aa
	in aa'
    printText0 ga (Logic_renaming aa ab ac _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	    ac' = printText0 ga ac
	in aa' <+> ab' <+> ac'

instance PrettyPrint RESTRICTION where
    printText0 ga (Hidden aa _) =
	let aa' = printText0 ga aa
	in aa'
    printText0 ga (Revealed aa _) =
	let aa' = printText0 ga aa
	in aa'
    printText0 ga (Logic_hiding aa ab ac _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	    ac' = printText0 ga ac
	in aa' <+> ab' <+> ac'

instance PrettyPrint SPEC_DEFN where
    printText0 ga (Spec_defn aa ab ac _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	    ac' = printText0 ga ac
	in aa' <+> ab' <+> ac'

instance PrettyPrint GENERICITY where
    printText0 ga (Genericity aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'

instance PrettyPrint PARAMS where
    printText0 ga (Params aa) =
	let aa' = printText0 ga aa
	in aa'

instance PrettyPrint IMPORTED where
    printText0 ga (Imported aa) =
	let aa' = printText0 ga aa
	in aa'

instance PrettyPrint FIT_ARG where
    printText0 ga (Fit_spec aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'
    printText0 ga (Fit_view aa ab _ ad) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	    ad' = printText0 ga ad
	in aa' <+> ab' <+> ad'

instance PrettyPrint VIEW_DEFN where
    printText0 ga (View_defn aa ab ac ad _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	    ac' = printText0 ga ac
	    ad' = printText0 ga ad
	in aa' <+> ab' <+> ac' <+> ad'

instance PrettyPrint VIEW_TYPE where
    printText0 ga (View_type aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'



