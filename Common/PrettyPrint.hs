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

class Gen1PrettyPrint s => Gen1PrintLaTeX s where
    gen1PrintLatex0 :: PrintLaTeX a => GlobalAnnos -> s a -> Doc

class Gen2PrettyPrint s => Gen2PrintLaTeX s where
    gen2PrintLatex0 :: (PrintLaTeX a,PrintLaTeX b) => 
                       GlobalAnnos -> s a b -> Doc

class Gen3PrettyPrint s => Gen3PrintLaTeX s where
    gen3PrintLatex0 :: (PrintLaTeX a,PrintLaTeX b, PrintLaTeX c) => 
                       GlobalAnnos -> s a b c -> Doc

-- This type class allows pretty printing of instantiating Datatypes
class Show a => PrettyPrint a where
    printText0 :: GlobalAnnos -> a -> Doc

class Gen1Show s where
    gen1ShowsPrec :: Show a => Int -> s a -> ShowS
    gen1Show      :: Show a => s a   -> String
    gen1ShowList  :: Show a => [s a] -> ShowS

    gen1ShowsPrec _ x s = gen1Show x ++ s
    gen1Show x          = gen1Shows x ""
    gen1ShowList ls   s = gen1ShowList__ gen1Shows ls s

gen1ShowList__ :: Show a => (s a -> ShowS) ->  [s a] -> ShowS
gen1ShowList__ _     []     s = "[]" ++ s
gen1ShowList__ gen1Showx (x:xs) s = '[' : gen1Showx x (gen1Showl xs)
  where
    gen1Showl []     = ']' : s
    gen1Showl (y:ys) = ',' : gen1Showx y (gen1Showl ys)
  
gen1Shows           :: (Gen1Show s, Show a) => s a -> ShowS
gen1Shows           =  gen1ShowsPrec 0

class Gen1Show s => Gen1PrettyPrint s where
    gen1PrintText0 :: PrettyPrint a => GlobalAnnos -> s a -> Doc

-- 2 type parameters
class Gen2Show s where
    gen2ShowsPrec :: (Show a, Show b) => Int -> s a b -> ShowS
    gen2Show      :: (Show a, Show b) => s a b   -> String
    gen2ShowList  :: (Show a, Show b) => [s a b] -> ShowS

    gen2ShowsPrec _ x s = gen2Show x ++ s
    gen2Show x          = gen2Shows x ""
    gen2ShowList ls   s = gen2ShowList__ gen2Shows ls s

gen2ShowList__ :: (Show a, Show b) => (s a b -> ShowS) ->  [s a b] -> ShowS
gen2ShowList__ _     []     s = "[]" ++ s
gen2ShowList__ gen2Showx (x:xs) s = '[' : gen2Showx x (gen2Showl xs)
  where
    gen2Showl []     = ']' : s
    gen2Showl (y:ys) = ',' : gen2Showx y (gen2Showl ys)
  
gen2Shows           :: (Gen2Show s, Show a, Show b) => s a b -> ShowS
gen2Shows           =  gen2ShowsPrec 0

class Gen2Show s => Gen2PrettyPrint s where
    gen2PrintText0 :: (PrettyPrint a, PrettyPrint b) => 
                      GlobalAnnos -> s a b -> Doc

-- 3 type parameters
class Gen3Show s where
    gen3ShowsPrec :: (Show a, Show b, Show c) => Int -> s a b c -> ShowS
    gen3Show      :: (Show a, Show b, Show c) => s a b c   -> String
    gen3ShowList  :: (Show a, Show b, Show c) => [s a b c] -> ShowS

    gen3ShowsPrec _ x s = gen3Show x ++ s
    gen3Show x          = gen3Shows x ""
    gen3ShowList ls   s = gen3ShowList__ gen3Shows ls s

gen3ShowList__ :: (Show a, Show b, Show c) => 
                  (s a b c -> ShowS) ->  [s a b c] -> ShowS
gen3ShowList__ _     []     s = "[]" ++ s
gen3ShowList__ gen3Showx (x:xs) s = '[' : gen3Showx x (gen3Showl xs)
  where
    gen3Showl []     = ']' : s
    gen3Showl (y:ys) = ',' : gen3Showx y (gen3Showl ys)
  
gen3Shows           :: (Gen3Show s, Show a, Show b, Show c) => s a b c -> ShowS
gen3Shows           =  gen3ShowsPrec 0

class Gen3Show s => Gen3PrettyPrint s where
    gen3PrintText0 :: (PrettyPrint a, PrettyPrint b, PrettyPrint c) => 
                      GlobalAnnos -> s a b c -> Doc

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
	printId printText0 ga Nothing (error "Common.PrettyPrint: Id") i

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
    printText0 _ga _s = empty

instance PrintLaTeX () where
    printLatex0 _ga _s = empty

instance (PrettyPrint a, PrettyPrint b) => PrettyPrint (Either a b) where
    printText0 ga (Left x) = printText0 ga x
    printText0 ga (Right x) = printText0 ga x

instance (PrintLaTeX a, PrintLaTeX b) => PrintLaTeX (Either a b) where
    printLatex0 ga (Left x) = printLatex0 ga x
    printLatex0 ga (Right x) = printLatex0 ga x

instance PrettyPrint a => PrettyPrint (Maybe a) where
    printText0 ga (Just x) = printText0 ga x
    printText0 _ Nothing = empty

instance PrintLaTeX a => PrintLaTeX (Maybe a) where
    printLatex0 ga (Just x) = printLatex0 ga x
    printLatex0 _ Nothing = empty
