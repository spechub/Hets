
{- HetCATS/Print_AS_Annotation.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   This module contains all instances of PrettyPrint for AS_Annotation.hs 

   todo:
      - LaTeX Pretty Printing
-}

module Common.Print_AS_Annotation where

import Common.AS_Annotation

import Common.GlobalAnnotations

import Common.Id (Id(..),splitMixToken)
import Common.PrettyPrint
import Common.Lib.Pretty
import Common.Lexer(whiteChars)
import Common.LaTeX_funs
import Data.Maybe(fromJust)

infixl 6 <\\+>


instance PrettyPrint Annotation where
    printText0 _ (Unparsed_anno aw at _) =
	case at of 
		Line_anno str -> 
		    (case aw of 
			    Comment_start -> ptext "%%"
		            Annote_word w ->  ptext $ "%" ++ w) 
		    <> (if all (`elem` whiteChars) str 
			then empty else ptext str)
		Group_anno strs -> 
		    let lns = vcat $ map ptext strs in
		    case aw of 
			    Comment_start -> ptext "%{" <> lns <> ptext "}%"
			    Annote_word w -> ptext ("%" ++ w ++ "(")
					 <> lns <> ptext ")%"    
    printText0 ga (Display_anno aa ab _) =
	let aa' = printText0 ga aa
	    ab' = fcat $ punctuate space $ map printPair $ filter nullSnd ab
	in printGroup (ptext "display") $ aa' <+> ab'
	   where printPair (s1,s2) = ptext (showDF s1) <+> ptext s2
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
	let aa' = ptext $ showPrecRel pflag
	    ab' = fcat $ punctuate (comma <> space) $ map (printText0 ga) ab
	    ac' = fcat $ punctuate (comma <> space) $ map (printText0 ga) ac
	in  printGroup (ptext "prec") $ braces ab' <+> aa' <+> braces ac'
    printText0 ga (Assoc_anno as aa _) =
	printGroup (case as of ARight -> ptext "right_assoc"
		               ALeft -> ptext "left_assoc") $ fcat $ 
				punctuate (comma <> space) $ 
					  map (printText0 ga) aa
    printText0 _ (Label aa _) =
	let aa' = vcat $ map ptext aa
	in ptext "%(" <> aa' <> ptext ")%"
    printText0 _ (Semantic_anno sa _) =
	printLine (ptext $ fromJust $ lookup sa $ semantic_anno_table) empty
-- -------------------------------------------------------------------------
-- LaTeX pretty printing
-- -------------------------------------------------------------------------

    printLatex0 _ (Unparsed_anno aw at _) =
	case at of 
		Line_anno str ->
		    case aw of 
			    Comment_start -> 	
				hc_sty_comment 
				( hc_sty_small_keyword "\\%\\%" 
				  <> casl_comment_latex (escape_latex str))
			    Annote_word w -> printLatexLine w $ 
					     if all (`elem` whiteChars) str 
						then empty 
						else casl_annotation_latex 
							 (escape_latex str)
		Group_anno strs ->
		    case aw of 
		    Comment_start ->
			case strs of
			[] -> hc_sty_comment 
			      (hc_sty_small_keyword "\\%\\{" <\\+> 
				  hc_sty_small_keyword "\\}\\%")
			[x] -> hc_sty_comment (hc_sty_small_keyword "\\%\\{" <>
				  conv x <> hc_sty_small_keyword "\\}\\%")
			(x:xs) -> vcat (hc_sty_comment 
					(hc_sty_small_keyword "\\%\\{" <>
					conv x) 
					: map (hc_sty_comment . conv') xs) 
				  <> hc_sty_comment 
					 (hc_sty_small_keyword "\\}\\%")
			where conv  = casl_comment_latex . escape_latex
			      conv' s = casl_comment_latex "~~~~" <> conv s
		    Annote_word w -> printLatexGroup w $ vcat 
				     $ map (casl_annotation_latex 
					    . escape_latex) strs
    printLatex0 ga (Display_anno aa ab _) =
	let aa' = printSmallId_latex ga aa
	    ab' = fsep_latex $ map printPair $ filter nullSnd ab
	in printLatexGroup "display" $ aa' <\\+> ab'
	   where printPair (s1,s2) = la (showDF s1) <\\+> la s2
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
	let aa' = hc_sty_axiom $ showPrecRel pflag
	    p_list = (\l -> casl_comment_latex "\\{" <> l 
		                <> casl_comment_latex "\\}")
		     .fcat
		     .(punctuate (smallComma_latex<>smallSpace_latex))
		     .(map (printSmallId_latex ga))
	in  printLatexGroup "prec" $ p_list ab <\\+> aa' <\\+> p_list ac
    printLatex0 ga (Assoc_anno as aa _) =
	printLatexGroup (case as of 
			 ALeft -> "left\\_assoc"
			 ARight -> "right\\_assoc") $ fcat $
	punctuate (smallComma_latex<>smallSpace_latex) $ 
	map (printSmallId_latex ga) aa
    printLatex0 _ (Label aa _) =
	let aa' = vcat $ map (casl_annotation_latex . escape_latex) aa
	in latex_macro "\\`" <> printLatexGroup "" aa'
    printLatex0 _ (Semantic_anno sa  _) =
	printLatexLine (fromJust $ lookup sa semantic_anno_table)  empty

-- -------------------------------------------------------------------------
-- utilies
-- -------------------------------------------------------------------------

showDF :: Display_format -> String
showDF df = fromJust $ lookup df display_format_table

showPrecRel :: PrecRel -> String
showPrecRel p = case p of Lower -> "<"
			  Higher -> ">"
			  BothDirections -> "<>"
			  NoDirection -> error "showPrecRel"

printCommaIds :: GlobalAnnos -> [Id] -> Doc
printCommaIds ga = fcat . punctuate (comma <> space) . map (printText0 ga)

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
