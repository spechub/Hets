
{- HetCATS/Print_AS_Annotation.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   This module contains all instances of PrettyPrint for AS_Annotation.hs 

   todo:
      - LaTeX Pretty Printing
-}

module Print_AS_Annotation where

import AS_Annotation

import GlobalAnnotations

import Id (Id(..),splitMixToken, tokStr)
import PrettyPrint
import Pretty
import LaTeX_funs

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
	    ab' = vcat $ map ptext ab
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
    printText0 _ (Label aa _) =
	let aa' = vcat $ map ptext aa
	in ptext "%(" <> aa' <> ptext ")%"
    printText0 _ (Implies _) =
	printLine (ptext "implies") empty
    printText0 _ (Definitional _) =
	printLine (ptext "def") empty
    printText0 _ (Conservative _) =
	printLine (ptext "cons") empty
    printText0 _ (Monomorph _) =
	printLine (ptext "mono") empty

    printLatex0 _ (Comment_line aa _) =
	   hc_sty_plain_keyword "\\%\\%" 
	<> hc_sty_comment (casl_comment_latex (escape_latex aa)) 
	   -- <> ptext "\n"
    printLatex0 _ (Comment_group aa _) =
	let aa' = 
	      map (casl_comment_latex . escape_latex) aa
	    (first_l,rem_ls) = case aa' of
			       [] -> (empty,[])
			       _  -> (head aa',tail aa')
	in cat [hc_sty_plain_keyword "\\%\\{"<> first_l,
		nest 6 (vcat rem_ls)] <> hc_sty_plain_keyword "\\}\\%"
    printLatex0 _ (Annote_line aa ab _) =
	printLatexLine aa $ casl_annotation_latex (escape_latex ab)
    printLatex0 _ga (Annote_group aa ab _) =
	printLatexGroup aa $ 
			vcat $ map (casl_annotation_latex . escape_latex) ab
    printLatex0 ga (Display_anno aa ab _) =
	let aa' = printSmallId_latex ga aa
	    ab' = fsep_latex $ map printPair $ filter nullSnd ab
	in printLatexGroup "display" $ aa' <\+> ab'
	   where printPair (s1,s2) = la s1 <\+> la s2
		 la = casl_annotation_latex . escape_latex  
		 nullSnd (_,s2) = not $ null s2
    printLatex0 ga (String_anno aa ab _) =
	let aa' = printSmallId_latex ga aa
	    ab' = printSmallId_latex ga ab
	in printLatexLine "string" $ aa' <> comma_latex <\+> ab'
    printLatex0 ga (List_anno aa ab ac _) =
	let aa' = printSmallId_latex ga aa
	    ab' = printSmallId_latex ga ab
	    ac' = printSmallId_latex ga ac
	in printLatexLine "list" $ aa' <> comma_latex <\+> ab' 
	                          <> comma_latex <\+> ac'
    printLatex0 ga (Number_anno aa _) =
	let aa' = printSmallId_latex ga aa
	in printLatexLine "number" aa'
    printLatex0 ga (Float_anno aa ab _) =
	let aa' = printSmallId_latex ga aa
	    ab' = printSmallId_latex ga ab
	in printLatexLine "floating" $ aa' <> comma_latex <\+> ab'
    printLatex0 ga (Prec_anno pflag ab ac _) =
	let aa' = hc_sty_axiom $ if pflag then "<" else "<>"
	    p_list = braces_latex.fsep_latex.
		     (punctuate comma_latex).(map (printSmallId_latex ga))
	    ab' =  p_list ab
	    ac' =  p_list ac
	in  printLatexGroup "prec" $ ab' <\+> aa' <\+> ac'
    printLatex0 ga (Lassoc_anno aa _) =
	printLatexGroup "left_assoc" $ fsep_latex $
		     punctuate comma_latex $ map (printSmallId_latex ga) aa
    printLatex0 ga (Rassoc_anno aa _) =
	printLatexGroup "right_assoc" $ fsep_latex $
		     punctuate comma_latex $ map (printSmallId_latex ga) aa
    printLatex0 _ (Label aa _) =
	let aa' = vcat $ map (casl_annotation_latex . escape_latex) aa
	in latex_macro "\\hfill" <> hc_sty_plain_keyword "\\%(" 
	       <> aa' <> hc_sty_plain_keyword ")%"
    printLatex0 _ (Implies _) =
	printLatexLine "implies" empty
    printLatex0 _ (Definitional _) =
	printLatexLine "def" empty
    printLatex0 _ (Conservative _) =
	printLatexLine "cons" empty
    printLatex0 _ (Monomorph _) =
	printLatexLine "mono" empty

printSmallId_latex :: GlobalAnnos -> Id -> Doc
printSmallId_latex ga (Id tops ids _) =
    let ids' = case ids of
	       [] -> empty
	       _  -> brackets_latex $ fsep_latex $ 
			punctuate comma_latex $ map (printSmallId_latex ga) ids
	(ts,ps) = splitMixToken tops
	pr_tops = hcat . map (casl_annotation_latex . escape_latex . tokStr)
	ts' = pr_tops ts
	ps' = pr_tops ps
    in ts' <> ids' <> ps'

printGroup :: Doc -> Doc -> Doc
printGroup key grp = ptext "%" <> key <> ptext "(" <+> grp <> ptext ")%"

printLatexGroup :: String -> Doc -> Doc
printLatexGroup kw grp = 
      hc_sty_plain_keyword ("\\%"++kw++"(")<>hc_sty_annotation grp
    <>hc_sty_plain_keyword ")\\%"

printLine :: Doc -> Doc -> Doc
printLine key line = ptext "%" <> key <+> line -- <> ptext "\n"

printLatexLine :: String -> Doc -> Doc
printLatexLine kw line = 
    hc_sty_plain_keyword ("\\%"++kw) <\+> hc_sty_annotation line

instance PrettyPrint [Annotation] where
    printText0 ga l = (vcat $ map (printText0 ga) l) -- <> ptext "\n"

    printLatex0 ga l = (vcat $ map (printLatex0 ga) l) -- <> ptext "\n"

instance (PrettyPrint a) => PrettyPrint (Annoted a) where
    printText0 ga (Annoted i _ las ras) =
	let i'   = printText0 ga i
	    las' = printText0 ga las
	    (la,rras) = case ras of
			[]     -> (empty,[])
			r@(l:xs)
			    | isLabel l -> (printText0 ga l,xs)
			    | otherwise -> (empty,r)
	    ras' = printText0 ga rras
        in las' $+$ (hang i' 0 la) $$ ras'

    printLatex0 ga (Annoted i _ las ras) =
	let i'   = printLatex0 ga i
	    las' = printLatex0 ga las
	    (la,rras) = case ras of
			[]     -> (empty,[])
			r@(l:xs)
			    | isLabel l -> (printLatex0 ga l,xs)
			    | otherwise -> (empty,r)
	    ras' = printLatex0 ga rras
        in las' $+$ (hang_latex i' 0 la) $$ ras'

spAnnotedPrint :: (PrettyPrint a) => 
		    (forall b .PrettyPrint b => GlobalAnnos -> b -> Doc) ->
		    (Doc -> Doc -> Doc) -> -- ^ a function like <+> or <\+>
		    GlobalAnnos -> Doc -> Annoted a -> Doc
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
	    as' = if null as then empty else pf ga as
        in keyw `beside_` san $+$ as' $+$ i'
