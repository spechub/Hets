{- |
   Module      :  $Header$
   Copyright   :  (c) Klaus Lüttich, Christian Maeder and Uni Bremen 2002-2003 
   Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

   Maintainer  :  hets@tzi.de
   Stability   :  provisional
   Portability :  portable

   This classes needs to be instantiated for every datastructure in AS_*
   for LaTeX and isolatin-1 pretty printing. 
-}

module Common.PrettyPrint 
    ( showPretty
    , renderText 
    , PrettyPrint(..)
    , PrintLaTeX(..)
    , printText
    , isChar
    , textStyle
    , printId
    ) 
    where

import Common.Id
import Common.Lib.Pretty
import Common.GlobalAnnotations

-- This type class allows latex printing of instantiated Datatypes
class PrettyPrint a => PrintLaTeX a where
    printLatex0 :: GlobalAnnos -> a -> Doc

-- This type class allows pretty printing of instantiating Datatypes
class Show a => PrettyPrint a where
    printText0 :: GlobalAnnos -> a -> Doc

-- | printText uses empty global annotations
printText :: PrettyPrint a  => a -> Doc
printText = printText0 emptyGlobalAnnos

-- | a more pretty alternative for shows
showPretty :: PrettyPrint a => a -> ShowS
showPretty = shows . printText0 emptyGlobalAnnos 

textStyle :: Style
textStyle = style {lineLength=80, ribbonsPerLine= 1.19} 
-- maximum line length 80 with 67 printable chars (up to 13 indentation chars) 

renderText :: Maybe Int -> Doc -> String
renderText mi d = fullRender (mode           textStyle')
		             (lineLength     textStyle')
			     (ribbonsPerLine textStyle')
			     string_txt_comp
			     ""
			     d 
		  
    where textStyle' = textStyle {lineLength = 
				        maybe (lineLength textStyle) id mi}
	  string_txt_comp td = case td of
			       Chr  c -> showChar   c
			       Str  s -> showString s
			       PStr s -> showString s

-- moved instance from Id.hs (to avoid cyclic imports via GlobalAnnotations)
instance PrettyPrint Token where
    printText0 _ = ptext . tokStr

isChar :: Token -> Bool
isChar t = take 1 (tokStr t) == "\'"

instance PrettyPrint Id where
    printText0  ga i = 
	printId printText0 ga Nothing undefined i

printId :: (GlobalAnnos -> Token -> Doc) -- ^ function to print a Token
	   -> GlobalAnnos -> (Maybe Display_format) 
	   -> ([Token] -> Doc)    -- ^ function to join translated tokens
	   -> Id -> Doc

printId pf ga mdf f i =
    let glue_tok pf' = hcat . map pf'
	print_ (Id tops_p ids_p _) = 
	    if null ids_p then glue_tok (pf ga) tops_p 
	    else let (toks, places) = splitMixToken tops_p
		     comp = pf ga (mkSimpleId "[") <> 
		            fcat (punctuate (pf ga $ mkSimpleId ",") 
				            $ map (printId pf ga mdf f) ids_p)
			    <> pf ga (mkSimpleId "]")
		 in fcat [glue_tok (pf ga) toks, comp, 
			  glue_tok (pf ga) places]
	in maybe (print_ i) 
	   ( \ df -> maybe (print_ i) f
	     $ lookupDisplay ga df i) mdf

instance PrettyPrint () where
   printText0 _ga _s = text "()"

instance PrintLaTeX () where
   printLatex0 _ga _s = text ""
