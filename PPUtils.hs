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

module PPUtils where
 
import AS_Annotation
import GlobalAnnotations

import Print_AS_Annotation
import Pretty
import PrettyPrint

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
-- greater than zero. It returns empty if the list and all nested lists
-- have only one element. If the list or an nested list has more than one
-- element a Doc containig one "s" is returned. 
pluralS :: ListCheck a => [a] -> Doc
pluralS l = 
    if length l > 1 then lastS 
    else case l of 
	     [x] -> if x `innerListGT` 1 then lastS 
		    else empty
	     _ -> error "pluralS do not accept list with zero elements"
    where lastS = char 's' 

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

sp_between :: String -> String -> Doc -> Doc
sp_between lb rb p = sp_hang (sp_hang (ptext lb) 1 p) 0 (ptext rb)

-- |
-- like punctuate from Pretty, but prepends symbol to every element 
-- omitting the first element 
prepPunctuate :: Doc -> [Doc] -> [Doc]
prepPunctuate _ [] = []
prepPunctuate symb (x:xs) = x:map (\e -> symb <> e) xs

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
		   vcat $ map (\x -> pf ga (l_annos x) 
			       $$ pf ga (item x) <> semi 
			       <+> pf ga (r_annos x)) 
		              (init l) ++ [pf ga (last l)]
