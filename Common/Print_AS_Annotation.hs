
{- HetCATS/Print_AS_Annotation.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   This module contains all instances of PrettyPrint for AS_Annotation.hs 

   todo:
      - LaTeX Pretty Printing
-}

module Common.Print_AS_Annotation where

import Data.Char (isSpace)

import Common.AS_Annotation

import Common.GlobalAnnotations

import Common.Id (Id(..),splitMixToken)
import Common.PrettyPrint
import Common.Lib.Pretty
import Common.LaTeX_funs

infixl 6 <\\+>

instance PrettyPrint Annotation where
    printText0 _ (Comment_line aa _) =
	ptext "%%" <> ptext aa -- <> ptext "\n"
    printText0 _ (Comment_group aa _) =
	let aa' = vcat $ map ptext aa
	in ptext "%{" <> aa' <> ptext "}%"
    printText0 _ (Annote_line aa ab _) =
	printLine (ptext aa) $ if all isSpace ab then empty else ptext ab
    printText0 _ (Annote_group aa ab _) =
	let aa' = ptext aa
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
	hc_sty_comment (   hc_sty_small_keyword "\\%\\%" 
			<> casl_comment_latex (escape_latex aa)) 
	   -- <> ptext "\n"
    printLatex0 _ (Comment_group ls _) =
	case ls of
	[]     -> hc_sty_comment (hc_sty_small_keyword "\\%\\{" <\\+> 
				  hc_sty_small_keyword "\\}\\%")
	[x]    -> hc_sty_comment (hc_sty_small_keyword "\\%\\{" <>
				  conv x <>
				  hc_sty_small_keyword "\\}\\%")
	(x:xs) -> vcat (hc_sty_comment (hc_sty_small_keyword "\\%\\{" <>
					conv x)
			  :map (hc_sty_comment . conv') xs) 
		  <> hc_sty_comment (hc_sty_small_keyword "\\}\\%")
	where conv  = casl_comment_latex . escape_latex
	      conv' s = casl_comment_latex "~~~~" <> conv s
	{- let aa' = 
	      map (casl_comment_latex . escape_latex) aa
	    (first_l,rem_ls) = case aa' of
			       [] -> (empty,[])
			       _  -> (head aa',tail aa')
	in hc_sty_comment $ -- TODO: Correct this!!
	   cat [hc_sty_small_keyword "\\%\\{"<> first_l,
		nest 6 (vcat rem_ls)] <> hc_sty_small_keyword "\\}\\%" -}
    printLatex0 _ (Annote_line aa ab _) =
	printLatexLine aa $ if all isSpace ab 
		            then empty 
		            else casl_annotation_latex (escape_latex ab)
    printLatex0 _ga (Annote_group aa ab _) =
	printLatexGroup aa $ 
			vcat $ map (casl_annotation_latex . escape_latex) ab
    printLatex0 ga (Display_anno aa ab _) =
	let aa' = printSmallId_latex ga aa
	    ab' = fsep_latex $ map printPair $ filter nullSnd ab
	in printLatexGroup "display" $ aa' <\\+> ab'
	   where printPair (s1,s2) = la s1 <\\+> la s2
		 la = casl_annotation_latex . escape_latex  
		 nullSnd (_,s2) = not $ null s2
    printLatex0 ga (String_anno aa ab _) =
	let aa' = printSmallId_latex ga aa
	    ab' = printSmallId_latex ga ab
	in printLatexLine "string" $ aa' <> smallComma_latex <\\+> ab'
    printLatex0 ga (List_anno aa ab ac _) =
	let aa' = printSmallId_latex ga aa
	    ab' = printSmallId_latex ga ab
	    ac' = printSmallId_latex ga ac
	in printLatexLine "list" $ aa' <> smallComma_latex <\\+> ab' 
	                          <> smallComma_latex <\\+> ac'
    printLatex0 ga (Number_anno aa _) =
	let aa' = printSmallId_latex ga aa
	in printLatexLine "number" aa'
    printLatex0 ga (Float_anno aa ab _) =
	let aa' = printSmallId_latex ga aa
	    ab' = printSmallId_latex ga ab
	in printLatexLine "floating" $ aa' <> smallComma_latex <\\+> ab'
    printLatex0 ga (Prec_anno pflag ab ac _) =
	let aa' = hc_sty_axiom $ if pflag then "<" else "<>"
	    p_list = (\l -> casl_comment_latex "\\{" <> l 
		                <> casl_comment_latex "\\}")
		     .fcat
		     .(punctuate (smallComma_latex<>smallSpace_latex))
		     .(map (printSmallId_latex ga))
	in  printLatexGroup "prec" $ p_list ab <\\+> aa' <\\+> p_list ac
    printLatex0 ga (Lassoc_anno aa _) =
	printLatexGroup "left\\_assoc" $ fcat $
	punctuate (smallComma_latex<>smallSpace_latex) $ 
	map (printSmallId_latex ga) aa
    printLatex0 ga (Rassoc_anno aa _) =
	printLatexGroup "right\\_assoc" $ fcat $
	punctuate (smallComma_latex<>smallSpace_latex) $
	map (printSmallId_latex ga) aa
    printLatex0 _ (Label aa _) =
	let aa' = vcat $ map (casl_annotation_latex . escape_latex) aa
	in latex_macro "\\`" <> printLatexGroup "" aa'
    printLatex0 _ (Implies _) =
	printLatexLine "implies" empty
    printLatex0 _ (Definitional _) =
	printLatexLine "def" empty
    printLatex0 _ (Conservative _) =
	printLatexLine "cons" empty
    printLatex0 _ (Monomorph _) =
	printLatexLine "mono" empty

smallSpace_latex :: Doc
smallSpace_latex = casl_comment_latex " "

smallComma_latex :: Doc
smallComma_latex = casl_comment_latex ","

(<\\+>) :: Doc -> Doc -> Doc
d1 <\\+> d2 = if isEmpty d1 
	     then (if isEmpty d2 
		   then empty
		   else d2)
	     else (if isEmpty d2
		   then d1
		   else 
		   d1 <> smallSpace_latex <> d2)


printSmallId_latex :: GlobalAnnos -> Id -> Doc
printSmallId_latex ga (Id tops ids _) =
    let ids' = case ids of
	       [] -> empty
	       _  ->  ((\x -> casl_comment_latex "[" <> x 
		                  <> casl_comment_latex "]")
		       . fcat 
		       . punctuate smallComma_latex 
		       . map (printSmallId_latex ga)) ids
	(ts,ps) = splitMixToken tops
	pr_tops = hcat . map (printToken_latex casl_annotation_latex)
    in pr_tops ts <> ids' <> pr_tops ps

printGroup :: Doc -> Doc -> Doc
printGroup key grp = ptext "%" <> key <> ptext "(" <+> grp <> ptext ")%"

printLatexGroup :: String -> Doc -> Doc
printLatexGroup kw grp = 
    hc_sty_annotation (  hc_sty_small_keyword ("\\%"++kw++"(")<>grp
		       <> hc_sty_small_keyword ")\\%")

printLine :: Doc -> Doc -> Doc
printLine key line = if isEmpty line then pkey else pkey <+> line
    where pkey = ptext "%" <> key

printLatexLine :: String -> Doc -> Doc
printLatexLine kw line = 
    hc_sty_annotation (if isEmpty line then kw_d else kw_d <\+> line)
    where kw_d = hc_sty_small_keyword ("\\%"++kw)

printAnnotationList_Text0 :: GlobalAnnos -> [Annotation] -> Doc
printAnnotationList_Text0 ga l = (vcat $ map (printText0 ga) l) 

printAnnotationList_Latex0 :: GlobalAnnos -> [Annotation] -> Doc
printAnnotationList_Latex0 ga l = (vcat $ map (printLatex0 ga) l) 

instance (PrettyPrint a) => PrettyPrint (Annoted a) where
    printText0 ga (Annoted i _ las ras) =
	let i'   = printText0 ga i
	    las' = printAnnotationList_Text0 ga las
	    (la,rras) = case ras of
			[]     -> (empty,[])
			r@(l:xs)
			    | isLabel l -> (printText0 ga l,xs)
			    | otherwise -> (empty,r)
	    ras' = printAnnotationList_Text0 ga rras
        in las' $+$ (hang i' 0 la) $$ ras'

    printLatex0 ga (Annoted i _ las ras) =
	let i'   = printLatex0 ga i
	    las' = printAnnotationList_Latex0 ga las
	    (la,rras) = case ras of
			[]     -> (empty,[])
			r@(l:xs)
			    | isLabel l -> (printLatex0 ga l,xs)
			    | otherwise -> (empty,r)
	    ras' =printAnnotationList_Latex0 ga rras
        in las' $+$ (hang_latex i' 0 la) $$ ras'
