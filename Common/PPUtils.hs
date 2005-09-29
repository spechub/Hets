{-| 
   
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  portable

Useful functions for pretty printing that will be allmost useful for
   many logics.

   Todo:
     - Add your own functions.
-}

module Common.PPUtils where

import Common.Id
import Common.AS_Annotation
import Common.GlobalAnnotations

import qualified Common.Lib.Set as Set
import qualified Common.Lib.Map as Map

import Common.Print_AS_Annotation
import Common.Lib.Pretty
import Common.PrettyPrint

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


instance ListCheck Token where
    _ `innerListGT` _ = False

instance ListCheck Id where
    _ `innerListGT` _ = False

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

-- | vertical composition with a specified number of blank lines
aboveWithNLs :: Int -> Doc -> Doc -> Doc
aboveWithNLs n d1 d2 = if isEmpty d2 then d1 else 
             if isEmpty d1 then d2 else 
             d1 $+$ foldr ($+$) d2 (replicate n $ text "")

infixl 5 $++$

-- | vertical composition with one blank line
($++$) :: Doc -> Doc -> Doc
($++$) = aboveWithNLs 1 

-- | list version of '($++$)'
vsep :: [Doc] -> Doc
vsep = foldr ($++$) empty

{- | the functions 'commaT_text', 'semiT_text', 'crossT_text' and 
     'semiAnno_text' are good for ASCII pretty printing 
      but don't work well for LaTeX output.
-}
commaT_text, semiT_text, crossT_text 
    :: PrettyPrint a => GlobalAnnos -> [a] -> Doc
commaT_text = listSep_text comma
semiT_text = listSep_text semi
crossT_text = listSep_text (space<>char '*')

listSep_text :: PrettyPrint a => Doc -> GlobalAnnos -> [a] -> Doc
listSep_text separator ga = fsep . punctuate separator . map (printText0 ga)

semiAnno_text :: PrettyPrint a => 
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
                                             (<+>) id empty
                                             ga (r_annos a_item)

{--------------------------------------------------------------------
  Lists
--------------------------------------------------------------------}

instance PrettyPrint a => PrettyPrint [a] where
  printText0 _ [] =  empty
  printText0 ga (x:xs) = 
    ptext "[" <+> commaT_text ga (x:xs) <+> ptext "]"
   
{--------------------------------------------------------------------
  Sets
--------------------------------------------------------------------}

instance PrettyPrint a => PrettyPrint (Set.Set a) where
  printText0 ga s  = printListSet ga True (Set.toAscList s)

-- | print a set without enclosing braces
printSet :: (PrettyPrint a) => GlobalAnnos -> Set.Set a -> Doc
printSet ga s = printListSet ga False (Set.toAscList s)

printListSet :: (PrettyPrint a) => GlobalAnnos -> Bool -> [a] -> Doc
printListSet _ False [] = empty     
printListSet _ True [] = ptext "{}" 
printListSet ga showBra (x:xs) 
  = (if showBra then ptext "{" else empty)
    <+> commaT_text ga (x:xs) 
    <+> (if showBra then ptext "}" else empty)
    

{--------------------------------------------------------------------
  Maps
--------------------------------------------------------------------}
instance (PrettyPrint k, PrettyPrint a) => PrettyPrint (Map.Map k a) where
  printText0 ga m  = printMap ga (Map.toAscList m)

printMap :: (PrettyPrint k,PrettyPrint a) => GlobalAnnos -> [(k,a)] -> Doc
printMap _ []     
  = ptext "{}" 
printMap ga (x:xs) 
  = ptext "{" <+> (fsep . punctuate comma . map printElem) (x:xs) <+>  ptext "}"
    where    
    printElem (k,v)  = printText0 ga k <+> ptext "|->" <+> printText0 ga v


{--------------------------------------------------------------------
  Pairs, triples
--------------------------------------------------------------------}
instance (PrettyPrint a, PrettyPrint b) => PrettyPrint (a,b) where
  printText0 ga (a,b) =
   ptext "(" <> printText0 ga a <> ptext "," <> printText0 ga b <> ptext ")"

instance (PrettyPrint a, PrettyPrint b, PrettyPrint c) => 
          PrettyPrint (a,b,c) where
  printText0 ga (a,b,c) =
   ptext "(" <> printText0 ga a <> ptext "," <> printText0 ga b 
             <> ptext "," <> printText0 ga c <> ptext ")"

{--------------------------------------------------------------------
  Simple types
--------------------------------------------------------------------}

instance PrettyPrint Bool where
  printText0 _ x = text $ show x
instance PrettyPrint Int where
  printText0 _ x = text $ show x
