
{- HetCATS/Print_AS_Annotation.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   This module contains all instances of PrettyPrint for AS_Annotation.hs 

   todo:
      - ATermConversion SML-CATS has now his own module 
        (s. HetCATS/aterm_conv/)
      - LaTeX Pretty Printing
-}

module Print_AS_Annotation where

import AS_Annotation
import Id
 
import PrettyPrint
import Pretty

instance PrettyPrint Annotation where
    printText0 ga (Comment_line aa _) =
	let aa' = printText0 ga aa
	in aa'
    printText0 ga (Comment_group aa _) =
	let aa' = printText0 ga aa
	in aa'
    printText0 ga (Annote_line aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'
    printText0 ga (Annote_group aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'
    printText0 ga (Display_anno aa ab _) =
	let aa' = printText0 ga aa
	    ab' = cat $ map printPair ab
	in aa' <+> ab'
	   where printPair (s1,s2) = ptext s1 <+> ptext s2
    printText0 ga (String_anno aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'
    printText0 ga (List_anno aa ab ac _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	    ac' = printText0 ga ac
	in aa' <+> ab' <+> ac'
    printText0 ga (Number_anno aa _) =
	let aa' = printText0 ga aa
	in aa'
    printText0 ga (Float_anno aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ab'
    printText0 ga (Prec_anno pflag ab ac _) =
	let aa' = if pflag then ptext "<" else ptext "<>"
	    ab' = printText0 ga ab
	    ac' = printText0 ga ac
	in  ab' <+> aa' <+> ac'
    printText0 ga (Lassoc_anno aa _) =
	let aa' = printText0 ga aa
	in aa'
    printText0 ga (Rassoc_anno aa _) =
	let aa' = printText0 ga aa
	in aa'
    printText0 ga (Label aa _) =
	let aa' = printText0 ga aa
	in aa'
    printText0 ga (Implies _) =
	empty
    printText0 ga (Definitional _) =
	empty
    printText0 ga (Conservative _) =
	empty

instance (PrettyPrint a) => PrettyPrint (Annoted a) where
    printText0 ga (Annoted i _ las ras) =
	let i'   = printText0 ga i
	    las' = printText0 ga las
	    ras' = printText0 ga ras
        in las' $$ i' <+> ras'

