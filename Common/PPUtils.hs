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

module Common.PPUtils (module Common.PPUtils,module Common.LaTeX_funs) where
 
import Common.Id
import Common.AS_Annotation
import Common.GlobalAnnotations

import Common.Print_AS_Annotation
import Common.Lib.Pretty
import Common.PrettyPrint

import Common.LaTeX_funs 		  

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
    if length l > 1 then lastS 
    else case l of 
	     [x] -> if x `innerListGT` 1 then lastS 
		    else ""
	     _ -> error "pluralS do not accept list with zero elements"
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
sp_brackets p = sp_hang (sp_hang lbrack 1 p) 0 rbrack

sp_braces :: Doc -> Doc 
sp_braces p = sp_hang (sp_hang lbrace 1 p) 0 rbrace

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

commaT,semiT,crossT :: PrettyPrint a => (GlobalAnnos -> a -> Doc) -> 
		       GlobalAnnos -> [a] -> Doc
commaT pf ga l = fsep $ punctuate comma $ map (pf ga) l

semiT pf ga l = fsep $ punctuate semi $ map (pf ga) l

crossT pf ga l = fsep $ punctuate (space<>char '*') $ map (pf ga) l

semiAnno :: (PrettyPrint a) => 
	    (forall b .PrettyPrint b => GlobalAnnos -> b -> Doc) ->  
	    GlobalAnnos -> [Annoted a] -> Doc
semiAnno pf ga l = if null l then 
		   empty 
		else 
		   vcat $ map (pf' True)
		              (init l) ++ [pf' False (last l)]
    where pf' printSemi a_item =
	      if printSemi 
	      then
	         pf ga (l_annos a_item)
			$$ pf ga (item a_item) <> semi 
			       <+>pf ga (r_annos a_item)
	      else 
	         pf ga (l_annos a_item) 
			$$ pf ga (item a_item) <+> pf ga (r_annos a_item) 
--------------------------------------------------------------------

-- | 
-- LaTeX variants of 'commaT' ...
commaT_latex,semiT_latex,crossT_latex 
    :: PrettyPrint a => (GlobalAnnos -> a -> Doc) -> 
                         GlobalAnnos -> [a] -> Doc
commaT_latex pf ga l = fsep_latex $ punctuate comma_latex $ map (pf ga) l

semiT_latex pf ga l = fsep_latex $ punctuate semi_latex $ map (pf ga) l

crossT_latex pf ga l = 
    fcat $ punctuate (space_latex 
		      <> hc_sty_axiom "\\times"<> space_latex) $ 
	       map (pf ga) l

semiAnno_latex :: (PrettyPrint a) => 
		  (forall b .PrettyPrint b => GlobalAnnos -> b -> Doc) ->  
		  GlobalAnnos -> [Annoted a] -> Doc
semiAnno_latex pf ga l = if null l then 
		   empty 
		else 
		   vcat $ map (pf' True)
		              (init l) ++ [pf' False (last l)]
    where pf' printSemi a_item =
	      if printSemi 
	      then
	         pf ga (l_annos a_item)
			$$ pf ga (item a_item) <> semi_latex
			       <\+> pf ga (r_annos a_item)
	      else 
	         pf ga (l_annos a_item) 
			$$ pf ga (item a_item) <\+> pf ga (r_annos a_item) 

hc_sty_casl_keyword :: String -> Doc
hc_sty_casl_keyword = hc_sty_keyword (Just "preds")

sp_hang_latex :: Doc -> Int -> Doc -> Doc
sp_hang_latex d1 n d2 = cat [d1, nest_latex n d2]

sp_between_latex :: Doc -> Doc -> Doc -> Doc
sp_between_latex lb rb p = sp_hang_latex (sp_hang_latex lb 1 p) 0 rb

sp_braces_latex :: Doc -> Doc
sp_braces_latex = 
    sp_between_latex (casl_normal_latex "\\{") (casl_normal_latex "\\}")

sp_brackets_latex :: Doc -> Doc
sp_brackets_latex =
    sp_between_latex (casl_normal_latex "[") (casl_normal_latex "]")

simple_id_latex :: SIMPLE_ID -> Doc 
simple_id_latex = hc_sty_structid . tokStr

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

tab_hang_latex :: Doc -> Int -> Doc -> Doc
tab_hang_latex d1 i d2 = sep_latex [d1, tab_nest_latex i d2]

{-nest_latex :: Int -> Doc -> Doc
nest_latex k = nest (k * space_latex_width)
     
hang_latex :: Doc -> Int -> Doc -> Doc
hang_latex d1 n d2 = sep_latex [d1, nest_latex n d2]
-}
