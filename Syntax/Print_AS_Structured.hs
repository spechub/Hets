{-| 
   
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

   Printing the Structured part of hetrogenous specifications.

   todo:
     - LaTeX Pretty Printing
-}

module Syntax.Print_AS_Structured where

import Common.Lib.Pretty
import Common.PrettyPrint
import Common.PPUtils

import Logic.Grothendieck

import Syntax.AS_Structured
import Common.Print_AS_Annotation
import Common.AS_Annotation
import Common.GlobalAnnotations

import Data.List
import Data.Maybe (fromMaybe)

import Debug.Trace

instance PrettyPrint SPEC where
    --- This implementation doesn't use the grouping information 
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
	fsep $ pl aa 
	where pl [] = [] 
	      pl (x:xs) =
		  (condBracesAnd printText0 sp_braces ga x):
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
	     condBracesGroupSpec printText0 braces Nothing ga aa
    printText0 ga (Local_spec aa ab _) =
	let aa' = printText0 ga aa
	    ab' = condBracesWithin printText0 sp_braces ga ab
	in (hang (ptext "local") 4 aa') $$ 
	   (hang (ptext "within") 4 ab')
    printText0 ga (Closed_spec aa _) =
	hang (ptext "closed") 4 $ 
	     condBracesGroupSpec printText0 braces Nothing ga aa
    printText0 ga (Group aa _) =
	printText0 ga aa
        -- maybe?: condBracesGroupSpec printText0 sp_braces ga aa
    printText0 ga (Spec_inst aa ab _) =
	let aa' = printText0 ga aa
	    ab' = print_fit_arg_list printText0 sp_brackets sep ga ab
	in nest 4 (hang aa' 4 ab')
    printText0 ga (Qualified_spec ln asp _) =
	ptext "logic" <+> (printText0 ga ln) <> colon $$ (printText0 ga asp)
    --- Another implementation of printText was deleted
    --- nobody wants to maintain almost duplicate code
    --- use global annotations for different printing options

    printLatex0 ga (Basic_spec aa) =
        tabbed_nest_latex $ printLatex0 ga aa
    printLatex0 ga (Translation aa ab) =
	let aa' = condBracesTransReduct printLatex0 
		           sp_braces_latex2 ga aa
	    ab' = printLatex0 ga ab
	in tab_hang_latex aa' 8 ab'
    printLatex0 ga (Reduction aa ab) =
	let aa' = condBracesTransReduct printLatex0 
		        sp_braces_latex2 ga aa
	    ab' = printLatex0 ga ab
	in tab_hang_latex aa' 8 ab'
    printLatex0 ga (Union aa _) = fsep_latex $ intersperse' aa 
	where intersperse' [] = [] 
	      intersperse' (x:xs) =
		  (condBracesAnd printLatex0 sp_braces_latex2 ga x):
		  map (\y -> hc_sty_plain_keyword "and" $$ 
		       condBracesAnd printLatex0 sp_braces_latex2 ga y)
                      xs
    printLatex0 ga (Extension aa _) =
	fsep_latex $ printList aa
	where printList [] = []
	      printList (x:xs) =
		  (sp_space <> printLatex0 ga' x):
		    map (spAnnotedPrint printLatex0 (<\+>) ga' 
			        (hc_sty_hetcasl_keyword "then")) xs
	      (sp_space,ga') = sp_space_latex ga
    printLatex0 ga (Free_spec aa _) =
	tabbed_nest_latex (condBracesGroupSpec printLatex0 
					  sp_braces_latex2 mkw ga aa)
	where mkw = 
		  mkMaybeKeywordTuple Nothing $ hc_sty_plain_keyword "free"
    printLatex0 ga (Local_spec aa ab _) =
	let aa' = sp_braces_latex2 $ set_tabbed_nest_latex $ 
	          (cond_space<> printLatex0 ga aa)
	    ab' = condBracesWithin printLatex0 sp_braces_latex2 ga ab
	    cond_space = case skip_Group $ item aa of
			 Extension _ _ -> space
			 Union _ _ -> space
			 _ -> empty
	    space = hspace_latex (
		       pt_length (keyword_width "view" + normal_width "~"))
		       <>setTab_latex
	in tabbed_nest_latex (setTabWithSpaces_latex 3<>
		 fsep [hc_sty_plain_keyword "local",tabbed_nest_latex aa',
		       hc_sty_plain_keyword "within",tabbed_nest_latex ab'])
    printLatex0 ga (Closed_spec aa _) =
	tabbed_nest_latex (condBracesGroupSpec printLatex0 
                                           sp_braces_latex2 mkw ga aa)
	where mkw = mkMaybeKeywordTuple Nothing
		    $ hc_sty_plain_keyword "closed"
    printLatex0 ga (Group aa _) =
	printLatex0 ga aa
    printLatex0 ga (Spec_inst aa ab _) =
	let aa' = simple_id_latex aa 
	    ga' = set_inside_gen_arg True (set_first_spec_in_param True ga) 
	in tabbed_nest_latex $
	   if null ab 
	   then aa' 
	   else aa' <\+> set_tabbed_nest_latex
		    (fsep_latex $ 
	              map (brackets_latex.
			   (\x -> set_tabbed_nest_latex
			          (printLatex0 ga' x))) ab)
	where ga' = set_inside_gen_arg True (set_first_spec_in_param True ga) 
    printLatex0 ga (Qualified_spec ln asp _) =
	hc_sty_plain_keyword "logic" <\+> 
            (printLatex0 ga ln) <> colon_latex $$ (printLatex0 ga asp)

instance PrettyPrint RENAMING where
    printText0 ga (Renaming aa _) =
	hang (text "with") 4 $ fcat $ map (printText0 ga) aa

    printLatex0 ga (Renaming aa _) =
       hc_sty_plain_keyword "with"<\+>
          set_tabbed_nest_latex (fsep_latex (map (printLatex0 ga) aa))


instance PrettyPrint RESTRICTION where
    printText0 ga (Hidden aa _) =
	hang (text "hide") 4 $ fsep $ condPunct comma aa 
                                                $ map (printText0 ga) aa
    printText0 ga (Revealed aa _) =
	hang (text "reveal") 4 $ printText0 ga aa

    printLatex0 ga (Hidden aa _) =
       hc_sty_plain_keyword "hide"<\+>
          set_tabbed_nest_latex 
                (fsep_latex (condPunct comma_latex 
                                       aa (map (printLatex0 ga) aa)))
    printLatex0 ga (Revealed aa _) =
	hc_sty_plain_keyword "reveal"<\+>
	  set_tabbed_nest_latex (printLatex0 ga aa)

condPunct :: Doc -> [G_hiding] -> [Doc] -> [Doc]
condPunct _ [] [] = []
condPunct _ _  [] = 
    error "something went wrong in printLatex0 of Hidden"
condPunct _ [] _  = 
    error "something went wrong in printLatex0 of Hidden"
condPunct _ [_c] [d] = [d]
condPunct com (c:cs) (d:ds) = 
		 (case c of
			G_symb_list _gsil -> d<>com 
			G_logic_projection _enc -> d)
		 : condPunct com cs ds


{- hang_latex (hc_sty_plain_keyword "reveal") 8 $ printLatex0 ga aa -}

{- Is declared in Print_AS_Library
instance PrettyPrint SPEC_DEFN where
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
	let aa' = set_tabbed_nest_latex $ printLatex0 ga aa
	    ab' = printLatex0 ga ab
	in if isEmpty aa' && isEmpty ab' 
	   then empty 
	   else 
	      if isEmpty aa' 
	      then ab' 
	      else if isEmpty ab' 
		   then aa' 
		   else fsep_latex [aa'<~>setTab_latex,
				    tabbed_nest_latex $ ab']

instance PrettyPrint PARAMS where
    printText0 ga (Params aa) =
	if null aa then empty
	else sep $ map (brackets.(nest (-4)).(printText0 ga)) aa

    printLatex0 ga (Params aa) =
	if null aa then empty
	else sep_latex $ 
	              map (brackets_latex.
			   (\x -> set_tabbed_nest_latex
			          (printLatex0 ga' x))) aa
	where ga' = set_inside_gen_arg True (set_first_spec_in_param True ga) 
instance PrettyPrint IMPORTED where
    printText0 ga (Imported aa) =
	if null aa then empty 
	else ptext "given" <+> (fsep $ punctuate comma $ 
				         map (condBracesGroupSpec printText0 
					         braces Nothing ga) aa)

    printLatex0 ga (Imported aa) =
	let mkw = mkMaybeKeywordTuple Nothing
		       (hc_sty_plain_keyword "given")
	    coBrGrSp = condBracesGroupSpec printLatex0 sp_braces_latex2
	    taa = tail aa
	    taa' = if null taa then [] 
		   else punctuate comma_latex $ tabList_latex $
			   map ( coBrGrSp Nothing ga) taa
	    condComma = if null taa then empty else comma_latex
	    aa' = fsep_latex (map (coBrGrSp Nothing ga) aa)
	in if null aa then empty 
	   else  fsep_latex ((coBrGrSp mkw ga (head aa) <> condComma): taa')
        
{-	tabbed_nest_latex (condBracesGroupSpec printLatex0 
					  sp_braces_latex2 mkw ga aa)
	where mkw = 
		  mkMaybeKeywordTuple Nothing $ hc_sty_plain_keyword "free"
-}
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
	    ad' = vcat $ map (printText0 ga) ad
	in ad' $$ hang (ptext "view" <+> aa') 4 ab'

    printLatex0 ga (Fit_spec aa ab _) =
	let aa' = printLatex0 ga aa
	    ab' = printLatex0 ga ab
	    null' = case ab of 
		    G_symb_map_items_list _ sis -> null sis
	in if null' then aa' 
	else fsep_latex [aa',
			     hc_sty_plain_keyword "fit"<\+>
			         set_tabbed_nest_latex ab']
    printLatex0 ga (Fit_view aa ab _ ad) =
	let aa' = simple_id_latex aa
	    ab' = print_fit_arg_list printLatex0 
	                             brackets_latex 
				     sep_latex
				     ga ab
	    ad' = vcat $ map (printLatex0 ga) ad
	    view_name = hc_sty_plain_keyword "view" <\+> aa'
	in ad' $$ if null ab then view_name else setTabWithSpaces_latex 16 <> tab_hang_latex view_name 16 ab'

{- This can be found in Print_AS_Library
instance PrettyPrint VIEW_DEFN where
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
print_fit_arg_list :: (GlobalAnnos -> (Annoted FIT_ARG) -> Doc)
		   -> (Doc -> Doc) -- ^ a function enclosing the Doc
                                   -- in brackets
		   -> ([Doc] -> Doc) -- ^ a function printing a list
                                     -- of Doc seperated by space
		   -> GlobalAnnos -> [Annoted FIT_ARG] -> Doc
print_fit_arg_list _pf _b_fun _sep_fun _ga [] = empty
print_fit_arg_list pf b_fun _sep_fun ga [fa] = b_fun $ pf ga fa
print_fit_arg_list pf b_fun sep_fun ga fas = 
    sep_fun $ map (b_fun . (pf ga)) fas

condBracesGroupSpec :: (GlobalAnnos -> (Annoted SPEC) -> Doc)
		    -> (Doc -> Doc) -- ^ a function enclosing the Doc
                                    -- in braces
		    -> Maybe (String,Doc) -- ^ something like a keyword 
					  -- that should be right before 
		                          -- the braces                        
		    -> GlobalAnnos -> (Annoted SPEC) -> Doc
condBracesGroupSpec pf b_fun mkeyw ga as =
    case skip_Group $ item as of
		 Spec_inst _ _ _ -> str_doc'<>as'
		 Union _ _       -> nested''
		 Extension _ _   -> nested''
		 _               -> 
		     if is_latex_print ga 
		     then str_doc'<>set_tabbed_nest_latex 
			              (b_fun (set_tabbed_nest_latex as'))
		     else str_doc'<>b_fun as'
    where as' = pf ga as
	  format_line = latex_macro (str++"\\{\\=\\KW{view}~\\=\\kill\n")
	  (str,str_doc) = fromMaybe ("",empty) mkeyw 
	  str_doc' = if isEmpty str_doc then empty 
	             else str_doc<>latex_macro"~"
	  nested' = format_line <> str_doc' <>
			      latex_macro "\\>"<>
				  tabbed_nest_latex(
				     b_fun (set_tabbed_nest_latex 
					    (latex_macro "\\>"<>as')))
	  nested'' = if is_latex_print ga then nested'
		     else str_doc' <>b_fun as'


condBracesTransReduct :: (GlobalAnnos -> (Annoted SPEC) -> Doc)
		      -> (Doc -> Doc) -- ^ a function enclosing the Doc
                                      -- in brackets
		      -> GlobalAnnos -> (Annoted SPEC) -> Doc
condBracesTransReduct pf b_fun ga as =
    case skip_Group $ item as of
		 Extension _ _    -> nested''
		 Union _ _        -> nested''
		 Local_spec _ _ _ -> nested''
		 _                -> as'
    where nested' =  tabbed_nest_latex
		      (format_line <>
		           b_fun (set_tabbed_nest_latex 
				     (latex_macro "\\>"<>as')))
          as' = pf ga as
	  format_line = latex_macro "\\{\\=\\KW{view}~\\=\\kill\n"	
	  nested'' = if is_latex_print ga then nested'
		     else b_fun as'

condBracesWithin :: (GlobalAnnos -> (Annoted SPEC) -> Doc)
		 -> (Doc -> Doc) -- ^ a function enclosing the Doc
                                 -- in braces
		 -> GlobalAnnos -> (Annoted SPEC) -> Doc
condBracesWithin pf b_fun ga as =
    case skip_Group $ item as of
		 Extension _ _    -> nested''
		 Union _ _        -> nested''
		 _                -> as'
    where nested' = 
		      (format_line <>
		           b_fun (set_tabbed_nest_latex  
				     (latex_macro "\\>"<>as')))
          as' = pf ga as
	  format_line = latex_macro "\\{\\=\\KW{view}~\\=\\kill\n"	
	  nested'' = if is_latex_print ga then nested'
		     else b_fun as'
	  b_fun' = if is_latex_print ga 
	           then b_fun . set_tabbed_nest_latex 
		   else b_fun

condBracesAnd :: (GlobalAnnos -> (Annoted SPEC) -> Doc)
	      -> (Doc -> Doc) -- ^ a function enclosing the Doc
                              -- in braces
	      -> GlobalAnnos -> (Annoted SPEC) -> Doc
condBracesAnd pf b_fun ga as =
    case skip_Group $ item as of
		 Extension _ _    -> nested''
		 _                -> as'
    where nested' = 
		      (format_line <>
		           b_fun (set_tabbed_nest_latex  
				     (latex_macro "\\>"<>as')))
          as' = pf ga as
	  format_line = latex_macro "\\{\\=\\KW{view}~\\=\\kill\n"	
	  nested'' = if is_latex_print ga then nested'
		     else b_fun as'
	  b_fun' = if is_latex_print ga 
	           then b_fun . set_tabbed_nest_latex 
		   else b_fun

skip_Group :: SPEC -> SPEC
skip_Group sp = 
    case sp of
	    Group as _ -> skip_Group $ item as
	    _          -> sp

mkMaybeKeywordTuple :: Maybe String -> Doc -> Maybe (String,Doc)
mkMaybeKeywordTuple mstr kw_doc = 
    Just (fromMaybe (if isEmpty kw_doc then "" 
		     else show $ kw_doc<~>setTab_latex) mstr,kw_doc)

sp_space_latex :: GlobalAnnos -> (Doc,GlobalAnnos)
sp_space_latex ga = if is_inside_gen_arg ga && is_first_spec_in_param ga
		    then (space,set_first_spec_in_param False ga)
		    else (empty,ga)
    where space = hspace_latex $ pt_length (keyword_width "view" + normal_width "~")

-- moved from Print_AS_Annotation
spAnnotedPrint :: (PrettyPrint a) => 
		    (forall b .PrettyPrint b => GlobalAnnos -> b -> Doc) 
		    -> (Doc -> Doc -> Doc) -- ^ a function like <+> or <\+>
		    -> GlobalAnnos -> Doc -> Annoted a -> Doc
spAnnotedPrint pf beside_ ga keyw ai = 
    case ai of 
    Annoted i _ las _ ->
	let i'   = pf ga i
            (msa,as) = case las of
		       []     -> (Nothing,[]) 
		       (x:xs) | isSemanticAnno x -> (Just x,xs)
		       xs     -> (Nothing,xs)
	    san      = case msa of
		       Nothing -> empty
		       Just a  -> pf ga a 
	    as' = if null as then empty else vcat $ map (pf ga) as
        in keyw `beside_` san $+$ as' $+$ i'
