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

import List

instance PrettyPrint SPEC where
    printText0 ga (Basic_spec aa) =
	printText0 ga aa
    printText0 ga (Translation aa ab) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' $$ ab'
    printText0 ga (Reduction aa ab) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' $$ ab'
    printText0 ga (Union aa _) =
	fsep $ intersperse (ptext "and") $ map (printText0 ga) aa
    printText0 ga (Extension aa _) =
	fsep $ intersperse (ptext "then") $ map (printText0 ga) aa
    printText0 ga (Free_spec aa _) =
	hang (ptext "free") 4 $ printText0 ga aa
    printText0 ga (Local_spec aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in (hang (ptext "local") 4 aa') $$ 
	   (hang (ptext "within") 4 ab')
    printText0 ga (Closed_spec aa _) =
	hang (ptext "closed") 4 $ printText0 ga aa
    printText0 ga (Group aa _) =
	braces $ printText0 ga aa
    printText0 ga (Spec_inst aa ab) =
	let aa' = printText0 ga aa
	    ab' = printText0_fit_arg_list ga ab
	in hang aa' 4 ab'

instance PrettyPrint RENAMING where
    printText0 ga (Renaming aa _) =
	hang (text "with") 4 $ printText0 ga aa
--	hang (text "with") 4 $ fcat $ 
--	     map (print_symb_map_items_text lid ga) aa
{-    printText0 ga (Logic_renaming l1 mor l2 _) =
	let l1'  = printText0 ga l1
	    mor' = printText0 ga mor
	    l2'  = printText0 ga l2 
	in hang (text "with logic") 4 (if null l1 then 
				         if null mor then ptext "-->" <+> l2'
				         else if null l2 then mor'
				              else mor' <+> ptext "->" <+> l2'
					else if null mor then 
					            l1' <+> text "-->" <+> l2'
					     else l1' <+> text "--" <+> 
					          mor' <+> text "->" <+> l2')
-}

instance PrettyPrint RESTRICTION where
{- <<<<<<< Print_AS_Structured.hs
    printText0 ga (Hidden (G_symb_items_list lid aa) _) =
	let aa' = hang (text "hide") 4 $ fcat $ 
	      punctuate comma $ map (print_symb_items_text lid ga) aa
	in aa'
    printText0 ga (Revealed (G_symb_map_items_list lid aa) _) =
	hang (text "reveal") 4 $ fcat $ 
	      punctuate comma $ map (print_symb_map_items_text lid ga) aa
-}
    printText0 ga (Hidden aa _) =
	hang (text "hide") 4 $ printText0 ga aa
    printText0 ga (Revealed aa _) =
	hang (text "reveal") 4 $ printText0 ga aa
{-    printText0 ga (Logic_hiding l1 mor l2 _) =
	hang (ptext "hide logic") 4 $ 
	     (if null l1 then 
	         if null mor then ptext "<--" <+> ptext l2
	         else
	            if null l2 then ptext mor 
	            else ptext mor <+> ptext "<-" <+> ptext l2 
	      else
	         if null mor then ptext l1 <+> ptext "<--" <+> ptext l2
	         else ptext l1 <+> ptext "<-" <+> 
	                 ptext mor <+> ptext "--" <+> ptext l2
	     )
-}
{- Is declared in Print_AS_Library
instance PrettyPrint SPEC_DEFN where
    printText0 ga (Spec_defn aa ab ac _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	    ac' = printText0 ga ac
	in aa' <+> ab' <+> ac'
-}

instance PrettyPrint G_mapping where
    printText0 ga (G_symb_map gsmil) = printText0 ga gsmil
    printText0 ga (G_logic_translation enc slog tlog _) =
	ptext "logic" {- TODO: implement right syntax. -}
		 -- pos: "logic",<encoding>,":",<src-logic>,"->",<targ-logic>


instance PrettyPrint G_hiding where
    printText0 ga (G_symb_list gsil) = printText0 ga gsil
    printText0 ga (G_logic_projection enc slog tlog _) = 
	ptext "logic" {- TODO: implement right syntax. -}
		 -- pos: "logic",<projection>,":",<src-logic>,"->",<targ-logic>

instance PrettyPrint GENERICITY where
    printText0 ga (Genericity aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in hang aa' 6 ab'

instance PrettyPrint PARAMS where
    printText0 ga (Params aa) =
	if null aa then empty
	else fcat $ punctuate space $ map (brackets . (printText0 ga)) aa

instance PrettyPrint IMPORTED where
    printText0 ga (Imported aa) =
	if null aa then empty 
	else ptext "given" <+> (fcat $ punctuate (comma <> space) $ 
				         map (printText0 ga) aa)

printText0_fit_arg_list ga [] = empty
printText0_fit_arg_list ga [fa] = brackets $ printText0 ga fa
printText0_fit_arg_list ga fas = 
    fsep $ map (brackets . (printText0 ga)) fas

instance PrettyPrint FIT_ARG where
    printText0 ga (Fit_spec aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
                         {- fcat $ punctuate (comma <> space) $ 
	                     map (print_symb_map_items_text lid ga) ab-}
	    null' = case ab of 
		    G_symb_map_items_list lid sis -> null sis
			-- null_symb_map_items_list lid sis
		    _ -> error $ "somthing very strange happend "++
			         "to G_symb_map_items_list"
	in aa' <+> if null' then empty else hang (ptext "fit") 4 ab'
    printText0 ga (Fit_view aa ab _ ad) =
	let aa' = printText0 ga aa
	    ab' = printText0_fit_arg_list ga ab
	    ad' = printText0 ga ad
	in ad' $$ hang (ptext "view" <+> aa') 4 ab'

{- This can be found in Print_AS_Library
instance PrettyPrint VIEW_DEFN where
    printText0 ga (View_defn aa ab ac ad _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	    ac' = printText0 ga ac
	    ad' = printText0 ga ad
	in aa' <+> ab' <+> ac' <+> ad'
-}

instance PrettyPrint VIEW_TYPE where
    printText0 ga (View_type aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in aa' <+> ptext "to" <+> ab'



