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
        text, char, 

	-- * Wrapping documents in delimiters
        parens, brackets, braces,

	-- * Combining documents
        (<>), 

	-- * Rendering documents

	render, fullRender, writeFileSDoc

--        TextDetails(..)

  ) where


import Prelude
import System.IO

infixl 6 <> 

-- ---------------------------------------------------------------------------
-- The interface

-- The primitive SDoc values

empty   :: SDoc;			-- ^ An empty document
comma   :: SDoc;                 -- ^ A ',' character

text	 :: String   -> SDoc
char 	 :: Char     -> SDoc


parens       :: SDoc -> SDoc; 	-- ^ Wrap document in @(...)@
brackets     :: SDoc -> SDoc;  	-- ^ Wrap document in @[...]@
braces	     :: SDoc -> SDoc;   	-- ^ Wrap document in @{...}@

-- Combining @SDoc@ values

(<>) :: SDoc -> SDoc -> SDoc;     -- ^Beside

-- Displaying @SDoc@ values. 

instance Show SDoc where
  showsPrec _prec doc cont = showSDoc doc cont

-- | Renders the document as a string using the default style
render     :: SDoc -> String

fullRender :: (String -> a -> a)   -- ^What to do with text
	   -> (a -> a -> a)             -- ^Compose two a
           -> a                         -- ^What to do at the end
           -> SDoc			-- ^The document
           -> a                         -- ^Result

comma = char ','

parens p        = char '(' <> p <> char ')'
brackets p      = char '[' <> p <> char ']'
braces p        = char '{' <> p <> char '}'

-- ---------------------------------------------------------------------------
-- The SDoc data type

-- A SDoc represents a *set* of layouts.  A SDoc with
-- no occurrences of Union or NoSDoc represents just one layout.

-- | The abstract type of documents
data SDoc
 = Empty                                -- empty
 | TextBeside String SDoc      -- text s <> x  
 | Beside SDoc SDoc                       

-- ---------------------------------------------------------------------------
-- @empty@, @text@

empty = Empty

char  c = TextBeside [c] Empty
text  s = TextBeside s Empty

-- ---------------------------------------------------------------------------
-- Horizontal composition @<>@

p <> q = Beside p q

-- ---------------------------------------------------------------------------
-- Displaying the best layout

writeFileSDoc :: FilePath -> SDoc -> IO ()
writeFileSDoc fp sd =
     do h <- openFile fp WriteMode
	fullRender (hPutTD h) (>>) (return ()) sd
	hClose h
    where hPutTD :: Handle -> String -> IO () -> IO ()
	  hPutTD h s io = hPutStr  h s >> io 

render doc       = showSDoc doc ""

showSDoc :: SDoc -> String -> String
showSDoc doc rest = fullRender showString (++) rest doc

fullRender = easy_display

easy_display :: (String -> a -> a)
	     -> (a -> a -> a)
             -> a                        
             -> SDoc			
             -> a                         
easy_display txt comp end doc 
  = lay doc 
  where
    lay Empty            = end
    lay (TextBeside s p) = s `txt` lay p
    lay (Beside p q)     = lay p `comp` lay q
