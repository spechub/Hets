{-| 
   
 > HetCATS/PPUtils.hs
 > $Id$
 > Authors: Klaus Lüttich
 > Year:    2002

   Useful functions for pretty printing that will be allmost useful for
   many logics.

   Todo:
     - Add your own functions.
-}

module Common.PPUtils (module Common.PPUtils,
		       module Common.LaTeX_funs,
		       hspace_latex) where

import Common.Id
import Common.AS_Annotation
import Common.GlobalAnnotations

import Common.Print_AS_Annotation
import Common.Lib.Pretty
import Common.PrettyPrint

import Common.LaTeX_funs hiding (startAnno,endAnno) 

-- | a helper type to pretty print (wrapped) strings 
data WrapString = WrapString String
instance Show WrapString where
    showsPrec _ (WrapString s) _ = s 

instance PrettyPrint WrapString where
    printText0 _ (WrapString s) = text s 

-- | 
-- a helper class for calculating the pluralS of e.g. ops
class ListCheck a where
    innerListGT :: a -> Int -> Bool

-- |
-- an instance of ListCheck for Annoted stuff 
instance ListCheck a => ListCheck (Annoted a) where
    ai `innerListGT` i =  (item ai) `innerListGT` i

-- |
-- pluralS checks a list with elements in class ListCheck for a list
-- greater than zero. It returns an empty String if the list and all
-- nested lists have only one element. If the list or an nested list
-- has more than one element a String containig one "s" is returned.
pluralS :: ListCheck a => [a] -> String
pluralS l = 
    case l of 
	   []  -> error "pluralS does not accept empty list"
	   [x] -> if x `innerListGT` 1 then lastS else ""
	   _   -> lastS
    where lastS = "s"

pluralS_doc :: ListCheck a => [a] -> Doc
pluralS_doc l = case pluralS l of
		"" -> empty
		s  -> ptext s

--------------------------------------------------------------------------

-- |
-- another hang function. This functions concats the documents if the line
-- has enough space left instead of seperating with a space. 
sp_hang :: Doc -> Int -> Doc -> Doc
sp_hang d1 n d2 = cat [d1, nest n d2]

-- |
-- only prints the brackets near to the enclosed document if all fits in 
-- one line otherwise the brackets stand alone and aligned one their own lines
-- and the enclosed document is nested one charcter wide.
sp_brackets :: Doc -> Doc 
sp_brackets p = sp_between lbrack rbrack p

sp_braces :: Doc -> Doc 
sp_braces p = sp_between lbrace rbrace p

sp_between :: Doc -> Doc -> Doc -> Doc
sp_between lb rb p = sp_hang (sp_hang lb 1 p) 0 rb

-- |
-- like punctuate from Pretty, but prepends symbol to every element 
-- omitting the first element 
prepPunctuate :: Doc -> [Doc] -> [Doc]
prepPunctuate _ [] = []
prepPunctuate symb (x:xs) = x:map (\e -> symb <> e) xs

-- | 
-- the functions 'commaT', 'semiT', 'crossT' and 'semiAnno' are good
-- for ASCII pretty printing but don't work well for LaTeX output.

commaT_text, semiT_text, crossT_text 
    :: PrettyPrint a => GlobalAnnos -> [a] -> Doc
commaT_text = listSep_text comma
semiT_text = listSep_text semi
crossT_text = listSep_text (space<>char '*')

listSep_text :: PrettyPrint a => Doc -> GlobalAnnos -> [a] -> Doc
listSep_text separator ga = fsep . punctuate separator . map (printText0 ga)

semiAnno_text :: (PrettyPrint a) => 
		 GlobalAnnos -> [Annoted a] -> Doc
semiAnno_text ga l = if null l then empty else
		     (vcat $ map (pf' True)
		      (init l) ++ [pf' False (last l)])
    where pfga as = vcat $ map (printText0 ga) as
	  pf' printSemi a_item =
	         pfga (l_annos a_item)
			$$ hang (printText0 ga (item a_item)
				 <> (if printSemi then semi else empty))
			       0 laImpl 
			$$ ras
	      where (laImpl,ras) = splitAndPrintRAnnos printText0 
	                                     printAnnotationList_Text0 
					     (<+>)
					     (empty) ga (r_annos a_item)

--------------------------------------------------------------------

-- | 
-- LaTeX variants of 'commaT' ...
commaT_latex,semiT_latex,crossT_latex 
    :: PrettyPrint a => GlobalAnnos -> [a] -> Doc

commaT_latex = listSep_latex comma_latex
semiT_latex = listSep_latex semi_latex
crossT_latex = listSep_latex 
	       (space_latex <> hc_sty_axiom "\\times"<> space_latex)

listSep_latex :: PrettyPrint a => Doc -> GlobalAnnos -> [a] -> Doc
listSep_latex separator ga = fsep_latex . punctuate separator .
			     map (printLatex0 ga)


semiAnno_latex :: (PrettyPrint a) => 
		  GlobalAnnos -> [Annoted a] -> Doc
semiAnno_latex ga l = if null l then empty else
		   (vcat $ map (pf' True)
		              (init l) ++ [pf' False (last l)])
    where pfga as = vcat $ map (printLatex0 ga) as
	  pf' printSemi a_item =
	      leftAF (rightAF (
		 if isEmpty laImpl then item'' else fsep_latex [item'', laImpl]))
	      where (laImpl,ras) = splitAndPrintRAnnos printLatex0 
	                                     printAnnotationList_Latex0 
					     (<\+>)
					     (latex_macro "\\`") 
					     ga (r_annos a_item)
		    item' = printLatex0 ga (item a_item)
		    item'' = if printSemi then item'<>semi_latex else item'
		    leftAF = if null l_annos' then id 
			                      else ($$) (pfga l_annos')
		    l_annos' = l_annos a_item
		    rightAF = if isEmpty ras then id
			                     else (\ x -> x $$ ras)

tabList_latex :: [Doc] -> [Doc]
tabList_latex [] = []
tabList_latex [x] = [startTab_latex <> x <> endTab_latex]
tabList_latex l = let h' = startTab_latex <> head l
		      l' = last l <>endTab_latex
		      rema = if null $ tail l 
			    then [] 
			    else init $ tail l 
		  in h':rema++[l']


hc_sty_casl_keyword :: String -> Doc
hc_sty_casl_keyword = hc_sty_keyword (Just "preds")

sp_hang_latex :: Doc -> Int -> Doc -> Doc
sp_hang_latex d1 n d2 = cat [d1, nest_latex n d2]

sp_between_latex :: Doc -> Doc -> Doc -> Doc
sp_between_latex lb rb p = sp_hang_latex (sp_hang_latex lb 1 p) 0 rb

sp_braces_latex :: Doc -> Doc
sp_braces_latex = 
    sp_between_latex (casl_normal_latex "\\{") (casl_normal_latex "\\}")

sp_braces_latex2 :: Doc -> Doc
sp_braces_latex2 d =
    fcat [casl_normal_latex "\\{"<>d,
	  casl_normal_latex "\\}"]

sp_brackets_latex :: Doc -> Doc
sp_brackets_latex =
    sp_between_latex (casl_normal_latex "[") (casl_normal_latex "]")

simple_id_latex :: SIMPLE_ID -> Doc 
simple_id_latex = hc_sty_structid . tokStr

simple_id_indexed_latex :: SIMPLE_ID -> Doc
simple_id_indexed_latex = hc_sty_structid_indexed . tokStr
parens_tab_latex :: Doc -> Doc
parens_tab_latex = parens_latex.set_tabbed_nest_latex

-- |
-- constant document to start indentation by a LaTeX tab stop
startTab_latex :: Doc
startTab_latex = latex_macro startTab

-- |
-- constant document to end indentation by a LaTeX tab stop
endTab_latex :: Doc
endTab_latex = latex_macro endTab

-- |
-- constant document to set a LaTeX tab stop at this position
setTab_latex :: Doc
setTab_latex = latex_macro setTab

setTabWithSpaces_latex :: Int -> Doc
setTabWithSpaces_latex = latex_macro . setTabWithSpaces

-- |
-- function for nice indentation
tabbed_nest_latex :: Doc -> Doc
tabbed_nest_latex d = startTab_latex <> d <> endTab_latex

-- |
-- function for nice indentation together with starting
set_tabbed_nest_latex :: Doc -> Doc
set_tabbed_nest_latex d = setTab_latex <> tabbed_nest_latex d 

tab_nest_latex :: Int -> Doc -> Doc
tab_nest_latex i d = tabbed_nest_latex (nest_latex i d)
{- tab_nest_latex i d =
   setTabWithSpaces_latex i <> tabbed_nest_latex (nest_latex i d)
-}
tab_hang_latex :: Doc -> Int -> Doc -> Doc
tab_hang_latex d1 i d2 = sep_latex [d1, tab_nest_latex i d2]
{-tab_hang_latex d1 i d2 = 
    setTabWithSpaces_latex i 
        <> sep_latex [d1, tabbed_nest_latex (nest_latex i d2)]
-}

