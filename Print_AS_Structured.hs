-- needs ghc -fglasgow-exts

{- HetCATS/Print_AS_Structured.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   Printing the Structured part of hetrogenous specifications.

   todo:
     - LaTeX Pretty Printing
-}

module Print_AS_Structured where

import Pretty
import PrettyPrint
import PPUtils

-- debugging stuff
--import IOExts (trace)

import Grothendieck

import AS_Structured
import Print_AS_Annotation
import AS_Annotation
import GlobalAnnotations
import List

instance PrettyPrint SPEC where
    --- This implementation don't uses the grouping information 
    --- it detects this information by precedence rules
    printText0 ga (Basic_spec aa) =
	nest 4 $ printText0 ga aa
    printText0 ga (Translation aa ab) =
	let aa' = condBracesTransReduct printText0 sp_braces ga aa
	    ab' = printText0 ga ab
	in hang aa' 4 ab'
    printText0 ga (Reduction aa ab) =
	let aa' = condBracesTransReduct printText0 sp_braces ga aa
	    ab' = printText0 ga ab
	in hang aa' 4 ab'
    printText0 ga (Union aa _) = 
	fsep $ intersperse' aa 
	where intersperse' [] = [] 
	      intersperse' (x:xs) =
		  (printText0 ga x):
		  map (\y -> ptext "and" $$ 
		       condBracesAnd printText0 sp_braces ga y) 
		      xs
    printText0 ga (Extension aa _) =
	fsep $ printList aa
	       -- intersperse (ptext "then") $ map (printText0 ga) aa
	where printList [] = []
	      printList (x:xs) = 
		  (printText0 ga x):
		    map (spAnnotedPrint printText0 (<+>) ga (ptext "then")) xs
    printText0 ga (Free_spec aa _) =
	hang (ptext "free") 5 $ 
	     condBracesGroupSpec printText0 sp_braces ga aa
    printText0 ga (Local_spec aa ab _) =
	let aa' = condBracesWithin printText0 sp_braces ga aa
	    ab' = condBracesWithin printText0 sp_braces ga ab
	in (hang (ptext "local") 4 aa') $$ 
	   (hang (ptext "within") 4 ab')
    printText0 ga (Closed_spec aa _) =
	hang (ptext "closed") 4 $ 
	     condBracesGroupSpec printText0 sp_braces ga aa
    printText0 ga (Group aa _) =
	printText0 ga aa
    printText0 ga (Spec_inst aa ab) =
	let aa' = printText0 ga aa
	    ab' = print_fit_arg_list printText0 sp_brackets sep ga ab
	in nest 4 (hang aa' 4 ab')
    printText0 ga (Qualified_spec ln asp _) =
	ptext "logic" <+> (printText0 ga ln) <> colon $$ (printText0 ga asp)
    --- Another implementation of printText 
    --- This implementation uses simply the supplied grouping information
    printText ga (Basic_spec aa) =
	nest 4 $ printText ga aa
    printText ga (Translation aa ab) =
	let aa' = printText ga aa
	    ab' = printText ga ab
	in hang aa' 4 ab'
    printText ga (Reduction aa ab) =
	let aa' = printText ga aa
	    ab' = printText ga ab
	in hang aa' 4 ab'
    printText ga (Union aa _) = 
	fsep $ intersperse' aa 
	where intersperse' [] = [] 
	      intersperse' (x:xs) =
		  (printText ga x):
		  map (\y -> ptext "and" $$ printText ga y) xs
    printText ga (Extension aa _) =
	fsep $ printList aa
	       -- intersperse (ptext "then") $ map (printText ga) aa
	where printList [] = []
	      printList (x:xs) = 
		  (printText ga x):
		    map (spAnnotedPrint printText (<+>) ga (ptext "then")) xs
    printText ga (Free_spec aa _) =
	hang (ptext "free") 5 $ printText ga aa
    printText ga (Local_spec aa ab _) =
	let aa' = printText ga aa
	    ab' = printText ga ab
	in (hang (ptext "local") 4 aa') $$ 
	   (hang (ptext "within") 4 ab')
    printText ga (Closed_spec aa _) =
	hang (ptext "closed") 4 $ printText ga aa
    printText ga (Group aa _) =
	lbrace $+$ printText ga aa $$ rbrace
    printText ga (Spec_inst aa ab) =
	let aa' = printText ga aa
	    ab' = print_fit_arg_list printText sp_brackets sep ga ab
	in nest 4 (hang aa' 4 ab')
    printText ga (Qualified_spec ln asp _) =
	ptext "logic" <+> (printText ga ln) <> colon $$ (printText ga asp)

     

    printLatex0 ga (Basic_spec aa) =
	hetcasl_nest_latex $ printLatex0 ga aa
    printLatex0 ga (Translation aa ab) =
	let aa' = condBracesTransReduct printLatex0 sp_braces_latex ga aa
	    ab' = printLatex0 ga ab
	in hang_latex aa' 8 ab'
    printLatex0 ga (Reduction aa ab) =
	let aa' = condBracesTransReduct printLatex0 sp_braces_latex ga aa
	    ab' = printLatex0 ga ab
	in hang_latex aa' 8 ab'
    printLatex0 ga (Union aa _) = fsep_latex $ intersperse' aa 
	where intersperse' [] = [] 
	      intersperse' (x:xs) =
		  (printLatex0 ga x):
		  map (\y -> hc_sty_plain_keyword "and" $$ 
		       condBracesAnd printLatex0 sp_braces_latex ga y)
                      xs
    printLatex0 ga (Extension aa _) =
	fsep_latex $ printList aa
	where printList [] = []
	      printList (x:xs) =
		  (printLatex0 ga x):
		    map (spAnnotedPrint printLatex0 (<\+>) ga 
			        (hc_sty_hetcasl_keyword "then")) xs
    printLatex0 ga (Free_spec aa _) =
	hang_latex (hc_sty_hetcasl_keyword "free") 8 $ 
	     condBracesGroupSpec printLatex0 sp_braces_latex ga aa
    printLatex0 ga (Local_spec aa ab _) =
	let aa' = condBracesWithin printLatex0 sp_braces_latex ga aa
	    ab' = condBracesWithin printLatex0 sp_braces_latex ga ab
	in (hang_latex (hc_sty_plain_keyword "local") 8 aa') $$ 
	   (hang_latex (hc_sty_plain_keyword "within") 8 ab')
    printLatex0 ga (Closed_spec aa _) =
	hang_latex (ptext "closed") 8 $ 
	     condBracesGroupSpec printLatex0 sp_braces_latex ga aa
    printLatex0 ga (Group aa _) =
	printLatex0 ga aa
    printLatex0 ga (Spec_inst aa ab) =
	let aa' = simple_id_latex aa
	    ab' = print_fit_arg_list printLatex0 
	                             sp_brackets_latex 
				     sep_latex
				     ga ab
	in hetcasl_nest_latex (hang_latex aa' 8 ab')
    printLatex0 ga (Qualified_spec ln asp _) =
	hc_sty_plain_keyword "logic" <\+> 
            (printLatex0 ga ln) <> colon_latex $$ (printLatex0 ga asp)

instance PrettyPrint RENAMING where
    printText0 ga (Renaming aa _) =
	hang (text "with") 4 $ cat $ map (printText0 ga) aa

    printLatex0 ga (Renaming aa _) =
	hang_latex (hc_sty_plain_keyword "with") 8 $ 
		   cat $ map (printLatex0 ga) aa

instance PrettyPrint RESTRICTION where
    printText0 ga (Hidden aa _) =
	hang (text "hide") 4 $ cat $ map (printText0 ga) aa
    printText0 ga (Revealed aa _) =
	hang (text "reveal") 4 $ printText0 ga aa

    printLatex0 ga (Hidden aa _) =
	hang_latex (hc_sty_plain_keyword "hide") 8 $ 
		   cat $ map (printLatex0 ga) aa
    printLatex0 ga (Revealed aa _) =
	hang_latex (hc_sty_plain_keyword "reveal") 8 $ printLatex0 ga aa

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
    printText0 ga (G_logic_translation enc) =
	ptext "logic" <+> printText0 ga enc

    printLatex0 ga (G_symb_map gsmil) = printLatex0 ga gsmil
    printLatex0 ga (G_logic_translation enc) =
	hc_sty_plain_keyword "logic" <\+> printLatex0 ga enc

instance PrettyPrint G_hiding where
    printText0 ga (G_symb_list gsil) = printText0 ga gsil
    printText0 ga (G_logic_projection enc) = 
	ptext "logic" <+> printText0 ga enc

    printLatex0 ga (G_symb_list gsil) = printLatex0 ga gsil
    printLatex0 ga (G_logic_projection enc) = 
	hc_sty_plain_keyword "logic" <\+> printLatex0 ga enc

instance PrettyPrint GENERICITY where
    printText0 ga (Genericity aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	in hang aa' 6 ab'

    printLatex0 ga (Genericity aa ab _) =
	let aa' = printLatex0 ga aa
	    ab' = printLatex0 ga ab
	in if isEmpty aa' && isEmpty ab' 
	   then empty 
	   else 
	      if isEmpty aa' 
	      then ab' 
	      else if isEmpty ab' 
		   then aa' 
		   else hang_latex aa' 10 ab'

instance PrettyPrint PARAMS where
    printText0 ga (Params aa) =
	if null aa then empty
	else sep $ map (sp_brackets.(nest (-4)).(printText0 ga)) aa

    printLatex0 ga (Params aa) =
	if null aa then empty
	else sep_latex $ map (sp_brackets_latex.params_nest_latex. 
			      (nest ((-5) * indent_mult)).(printLatex0 ga)) aa

instance PrettyPrint IMPORTED where
    printText0 ga (Imported aa) =
	if null aa then empty 
	else ptext "given" <+> (fsep $ punctuate comma $ 
				         map (condBracesGroupSpec printText0 
					         sp_braces ga) aa)

    printLatex0 ga (Imported aa) =
	if null aa then empty 
	else hc_sty_plain_keyword "given" <\+> 
		 (fsep_latex $ punctuate comma_latex $ 
		             map (condBracesGroupSpec printLatex0 
				      sp_braces_latex ga) aa)

instance PrettyPrint FIT_ARG where
    printText0 ga (Fit_spec aa ab _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	    null' = case ab of 
		    G_symb_map_items_list _ sis -> null sis
	in aa' <+> if null' then empty else hang (ptext "fit") 4 ab'
    printText0 ga (Fit_view aa ab _ ad) =
	let aa' = printText0 ga aa
	    ab' = print_fit_arg_list printText0 sp_brackets sep ga ab
	    ad' = printText0 ga ad
	in ad' $$ hang (ptext "view" <+> aa') 4 ab'

    printLatex0 ga (Fit_spec aa ab _) =
	let aa' = printLatex0 ga aa
	    ab' = printLatex0 ga ab
	    null' = case ab of 
		    G_symb_map_items_list _ sis -> null sis
	in aa' <\+> if null' then empty 
	            else hang_latex (hc_sty_plain_keyword "fit") 8 ab'
    printLatex0 ga (Fit_view aa ab _ ad) =
	let aa' = simple_id_latex aa
	    ab' = print_fit_arg_list printLatex0 
	                             sp_brackets_latex 
				     sep_latex
				     ga ab
	    ad' = printLatex0 ga ad
	in ad' $$ hang_latex (hc_sty_plain_keyword "view" <\+> aa') 8 ab'

{- This can be found in Print_AS_Library
instance PrettyPrint VIEW_DEFN where
    printText0 ga (View_defn aa ab ac ad _) =
	let aa' = printText0 ga aa
	    ab' = printText0 ga ab
	    ac' = printText0 ga ac
	    ad' = printText0 ga ad
	in aa' <+> ab' <+> ac' <+> ad'
-}

instance PrettyPrint Logic_code where
    printText0 ga (Logic_code (Just enc) (Just src) (Just tar) _) =
	printText0 ga enc <+> colon <+>
	printText0 ga src <+> ptext "->" <+>
	printText0 ga tar
    printText0 ga (Logic_code (Just enc) (Just src) Nothing _) =
	printText0 ga enc <+> colon <+>
	printText0 ga src <+> ptext "->"
    printText0 ga (Logic_code (Just enc) Nothing (Just tar) _) =
	printText0 ga enc <+> colon <+>
	ptext "->" <+> printText0 ga tar
    printText0 ga (Logic_code Nothing (Just src) (Just tar) _) =
	printText0 ga src <+> ptext "->" <+>
	printText0 ga tar
    printText0 ga (Logic_code (Just enc) Nothing Nothing _) =
	printText0 ga enc 
    printText0 ga (Logic_code Nothing (Just src) Nothing _) =
	printText0 ga src <+> ptext "->"
    printText0 ga (Logic_code Nothing Nothing (Just tar) _) =
	ptext "->" <+> printText0 ga tar
    printText0 _ (Logic_code Nothing Nothing Nothing _) =
	ptext ":ERROR" -- should not occur


    printLatex0 ga (Logic_code (Just enc) (Just src) (Just tar) _) =
	printLatex0 ga enc <\+> colon_latex <\+>
	printLatex0 ga src <\+> hc_sty_axiom "\\rightarrow" <\+>
	printLatex0 ga tar
    printLatex0 ga (Logic_code (Just enc) (Just src) Nothing _) =
	printLatex0 ga enc <\+> colon_latex <\+>
	printLatex0 ga src <\+> hc_sty_axiom "\\rightarrow"
    printLatex0 ga (Logic_code (Just enc) Nothing (Just tar) _) =
	printLatex0 ga enc <\+> colon <\+>
	hc_sty_axiom "\\rightarrow" <\+> printLatex0 ga tar
    printLatex0 ga (Logic_code Nothing (Just src) (Just tar) _) =
	printLatex0 ga src <\+> hc_sty_axiom "\\rightarrow" <\+>
	printLatex0 ga tar
    printLatex0 ga (Logic_code (Just enc) Nothing Nothing _) =
	printLatex0 ga enc 
    printLatex0 ga (Logic_code Nothing (Just src) Nothing _) =
	printLatex0 ga src <\+> hc_sty_axiom "\\rightarrow"
    printLatex0 ga (Logic_code Nothing Nothing (Just tar) _) =
	hc_sty_axiom "\\rightarrow" <\+> printLatex0 ga tar
    printLatex0 _ (Logic_code Nothing Nothing Nothing _) =
	ptext ":ERROR" -- should not occur

instance PrettyPrint Logic_name where
    printText0 ga (Logic_name mlog slog) =
        printText0 ga mlog <> 
		       (case slog of 
		       Nothing -> empty 
		       Just sub -> ptext "." <> printText0 ga sub)

    printLatex0 ga (Logic_name mlog slog) =
        printLatex0 ga mlog <> 
		       (case slog of 
		       Nothing -> empty 
		       Just sub -> casl_normal_latex "." <> printLatex0 ga sub)

-----------------------------------------------
print_fit_arg_list:: (GlobalAnnos -> (Annoted FIT_ARG) -> Doc) -> 
		     (Doc -> Doc) -> -- ^ a function enclosing the Doc
                                     -- in brackets
		     ([Doc] -> Doc) -> -- ^ a function printing a list
                                       -- of Doc seperated by space
		     GlobalAnnos -> [Annoted FIT_ARG] -> Doc
print_fit_arg_list _pf _b_fun _sep_fun _ga [] = empty
print_fit_arg_list pf b_fun _sep_fun ga [fa] = b_fun $ pf ga fa
print_fit_arg_list pf b_fun sep_fun ga fas = 
    sep_fun $ map (b_fun . (pf ga)) fas

condBracesGroupSpec :: (GlobalAnnos -> (Annoted SPEC) -> Doc) -> 
		     (Doc -> Doc) -> -- ^ a function enclosing the Doc
                                     -- in braces
		       GlobalAnnos -> (Annoted SPEC) -> Doc
condBracesGroupSpec pf b_fun ga as =
    case skip_Group $ item as of
		 Spec_inst _ _ -> as'
		 _             -> b_fun as'
    where as' = pf ga as

condBracesTransReduct :: (GlobalAnnos -> (Annoted SPEC) -> Doc) -> 
		     (Doc -> Doc) -> -- ^ a function enclosing the Doc
                                     -- in brackets
		       GlobalAnnos -> (Annoted SPEC) -> Doc
condBracesTransReduct pf b_fun ga as =
    case skip_Group $ item as of
		 Extension _ _    -> b_fun as'
		 Union _ _        -> b_fun as'
		 Local_spec _ _ _ -> b_fun as'
		 _                -> as'
    where as' = pf ga as

condBracesWithin :: (GlobalAnnos -> (Annoted SPEC) -> Doc) -> 
		    (Doc -> Doc) -> -- ^ a function enclosing the Doc
                                    -- in braces
		    GlobalAnnos -> (Annoted SPEC) -> Doc
condBracesWithin pf b_fun ga as =
    case skip_Group $ item as of
		 Extension _ _    -> b_fun as'
		 Union _ _        -> b_fun as'
		 _                -> as'
    where as' = pf ga as

condBracesAnd :: (GlobalAnnos -> (Annoted SPEC) -> Doc) -> 
		 (Doc -> Doc) -> -- ^ a function enclosing the Doc
                                 -- in braces
		 GlobalAnnos -> (Annoted SPEC) -> Doc
condBracesAnd pf b_fun ga as =
    case skip_Group $ item as of
		 Extension _ _    -> b_fun as'
		 _                -> as'
    where as' = pf ga as

skip_Group :: SPEC -> SPEC
skip_Group sp = 
    case sp of
	    Group as _ -> skip_Group $ item as
	    _          -> sp
