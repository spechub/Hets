
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
    printText0 _ (Comment_line aa _) =
	ptext "%%" <> ptext aa -- <> ptext "\n"
    printText0 _ (Comment_group aa _) =
	let aa' = vcat $ map ptext aa
	in ptext "%{" <> aa' <> ptext "}%"
    printText0 ga (Annote_line aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in ptext "%" <> aa' <+> ab' -- <> ptext "\n"
    printText0 ga (Annote_group aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in printGroup aa' ab'
    printText0 ga (Display_anno aa ab _) =
	let aa' = printText0 ga aa
	    ab' = fcat $ punctuate space $ map printPair $ filter nullSnd ab
	in printGroup (ptext "display") $ aa' <+> ab'
	   where printPair (s1,s2) = ptext s1 <+> ptext s2
		 nullSnd (_,s2) = not $ null s2
    printText0 ga (String_anno aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in printLine (ptext "string") $ aa' <> comma <+> ab'
    printText0 ga (List_anno aa ab ac _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	    ac' = printText0 ga ac
	in printLine (ptext "list") $ aa' <> comma <+> ab' <> comma <+> ac'
    printText0 ga (Number_anno aa _) =
	let aa' = printText0 ga aa
	in printLine (ptext "number") aa'
    printText0 ga (Float_anno aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in printLine (ptext "floating") $ aa' <> comma <+> ab'
    printText0 ga (Prec_anno pflag ab ac _) =
	let aa' = if pflag then ptext "<" else ptext "<>"
	    ab' = fcat $ punctuate (comma <> space) $ map (printText0 ga) ab
	    ac' = fcat $ punctuate (comma <> space) $ map (printText0 ga) ac
	in  printGroup (ptext "prec") $ braces ab' <+> aa' <+> braces ac'
    printText0 ga (Lassoc_anno aa _) =
	printGroup (ptext "left_assoc") $ fcat $ 
				punctuate (comma <> space) $ 
					  map (printText0 ga) aa
    printText0 ga (Rassoc_anno aa _) =
	printGroup (ptext "right_assoc") $ fcat $ 
				punctuate (comma <> space) $ 
					  map (printText0 ga) aa
    printText0 ga (Label aa _) =
	let aa' = printText0 ga aa
	in ptext "%(" <> aa' <> ptext ")%"
    printText0 _ (Implies _) =
	printLine (ptext "implies") empty
    printText0 _ (Definitional _) =
	printLine (ptext "def") empty
    printText0 _ (Conservative _) =
	printLine (ptext "cons") empty
    printText0 _ (Monomorph _) =
	printLine (ptext "mono") empty

printGroup :: Doc -> Doc -> Doc
printGroup key grp = ptext "%" <> key <> ptext "(" <+> grp <> ptext ")%"

printLine :: Doc -> Doc -> Doc
printLine key line = ptext "%" <> key <+> line -- <> ptext "\n"

instance PrettyPrint [Annotation] where
    printText0 ga l = (vcat $ map (printText0 ga) l) -- <> ptext "\n"

instance (PrettyPrint a) => PrettyPrint (Annoted a) where
    printText0 ga (Annoted i _ las ras) =
	let i'   = printText0 ga i
	    las' = printText0 ga las
	    ras' = printText0 ga ras
        in las' $+$ i' <+> ras'

