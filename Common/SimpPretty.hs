{-| 
   
Module      :  $Header$
Copyright   :  (c) Hughes, Peyton Jones, Klaus Lüttich, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   An imported and simplified version of GHC module
   
   GHCs documentation follows 

-}

-----------------------------------------------------------------------------
-- 
-- Module      :  Common.Lib.Pretty
-- Copyright   :  (c) The University of Glasgow 2001
-- License     :  BSD-style (see the file libraries/base/LICENSE)
-- 
-- Maintainer  :  libraries@haskell.org
-- Stability   :  provisional
-- Portability :  portable
--
-- John Hughes's and Simon Peyton Jones's Pretty Printer Combinators
-- 
-- Based on /The Design of a Pretty-printing Library/
-- in Advanced Functional Programming,
-- Johan Jeuring and Erik Meijer (eds), LNCS 925
-- <http://www.cs.chalmers.se/~rjmh/Papers/pretty.ps>
--
-- Heavily modified by Simon Peyton Jones, Dec 96
--
-----------------------------------------------------------------------------


module Common.SimpPretty (

	-- * The document type
        SDoc,            -- Abstract

	-- * Primitive SDocuments
        empty,comma,

	-- * Converting values into documents
        text, char, integer,

	-- * Wrapping documents in delimiters
        parens, brackets, braces,

	-- * Combining documents
        (<>), punctuate,

	-- * Predicates on documents
	isEmpty,

	-- * Rendering documents

	render, fullRender,writeFileSDoc,

        TextDetails(..)

  ) where


import Prelude
import System.IO

infixl 6 <> 

-- ---------------------------------------------------------------------------
-- The interface

-- The primitive SDoc values

isEmpty :: SDoc    -> Bool;  -- ^ Returns 'True' if the document is empty

empty   :: SDoc;			-- ^ An empty document
comma   :: SDoc;                 -- ^ A ',' character

text	 :: String   -> SDoc
char 	 :: Char     -> SDoc
integer  :: Integer  -> SDoc


parens       :: SDoc -> SDoc; 	-- ^ Wrap document in @(...)@
brackets     :: SDoc -> SDoc;  	-- ^ Wrap document in @[...]@
braces	     :: SDoc -> SDoc;   	-- ^ Wrap document in @{...}@

-- Combining @SDoc@ values

(<>)   :: SDoc -> SDoc -> SDoc;     -- ^Beside
punctuate :: SDoc -> [SDoc] -> [SDoc];      -- ^ @punctuate p [d1, ... dn] = [d1 \<> p, d2 \<> p, ... dn-1 \<> p, dn]@


-- Displaying @SDoc@ values. 

instance Show SDoc where
  showsPrec _prec doc cont = showSDoc doc cont

-- | Renders the document as a string using the default style
render     :: SDoc -> String

fullRender :: (TextDetails -> a -> a)   -- ^What to do with text
	   -> (a -> a -> a)             -- ^Compose two a
           -> a                         -- ^What to do at the end
           -> SDoc			-- ^The document
           -> a                         -- ^Result

comma = char ','

integer  n = text (show n)

parens p        = char '(' <> p <> char ')'
brackets p      = char '[' <> p <> char ']'
braces p        = char '{' <> p <> char '}'

punctuate _ []     = []
punctuate p (d:ds) = go d ds
                   where
                     go d1 [] = [d1]
                     go d1 (e:es) = (d1 <> p) : go e es

-- ---------------------------------------------------------------------------
-- The SDoc data type

-- A SDoc represents a *set* of layouts.  A SDoc with
-- no occurrences of Union or NoSDoc represents just one layout.

-- | The abstract type of documents
data SDoc
 = Empty                                -- empty
 | TextBeside TextDetails SDoc      -- text s <> x  
 | Beside SDoc SDoc                       

type RSDoc = SDoc         -- RSDoc is a "reduced SDoc", guaranteed not to have a top-level Above or Beside


reduceSDoc :: SDoc -> RSDoc
reduceSDoc (Beside p q) = beside p (reduceSDoc q)
reduceSDoc p              = p


data TextDetails = Chr  {-# UNPACK #-} !Char
                 | Str  {-# UNPACK #-} !String

        -- Arg of a TextBeside is always an RSDoc

{-textBeside_ :: TextDetails -> SDoc -> SDoc
textBeside_ s p = TextBeside s p
-}
-- ---------------------------------------------------------------------------
-- @empty@, @text@, @nest@, @union@

empty = Empty

isEmpty Empty = True
isEmpty _     = False

char  c = TextBeside (Chr c) Empty
text  s = TextBeside (Str s) Empty

-- ---------------------------------------------------------------------------
-- Horizontal composition @<>@

p <> q = Beside p q

beside :: SDoc -> RSDoc -> RSDoc
-- Specification: beside g p q = p <g> q
 
beside Empty             q   = q
beside (TextBeside s p) q   = TextBeside s rest
                               where
                                  rest = case p of
                                           Empty -> q
                                           _     -> beside p q
beside p q2 = beside (reduceSDoc p) q2

-- ---------------------------------------------------------------------------
-- Displaying the best layout

writeFileSDoc :: FilePath -> SDoc -> IO ()
writeFileSDoc fp sd =
     do h <- openFile fp WriteMode
	fullRender (hPutTD h) (>>) (return ()) sd
	hClose h
    where hPutTD :: Handle -> TextDetails -> IO () -> IO ()
	  hPutTD h td io = case td of
			 Chr  c -> hPutChar h c >> io
			 Str  s -> hPutStr  h s >> io

render doc       = showSDoc doc ""

showSDoc :: SDoc -> String -> String
showSDoc doc rest = fullRender string_txt_comp (++) rest doc

{-
string_txt (Chr c)   s  = c:s
string_txt (Str s1)  s2 = s1 ++ s2
string_txt (PStr s1) s2 = s1 ++ s2
-}
string_txt_comp :: TextDetails -> String -> String
string_txt_comp td = case td of
		     Chr  c -> showChar   c
		     Str  s -> showString s


fullRender txt comp end doc = easy_display txt comp end (doc)

easy_display :: (TextDetails -> a -> a)
	     -> (a -> a -> a)
             -> a                        
             -> SDoc			
             -> a                         
easy_display txt comp end doc 
  = lay doc 
  where
    lay Empty            = end
    lay (TextBeside s p) = s `txt` lay p
    lay (Beside Empty q) = lay q
    lay (Beside p Empty) = lay p
    lay (Beside p q)     = (lay p) `comp` (lay q) 
    lay _ = error "lay: Beside found"


