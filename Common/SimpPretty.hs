{-| 
   
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, C. Maeder Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  portable

A very simplified version of John Hughes's 
   and Simon Peyton Jones's Pretty Printer Combinators. Only catenable 
   string sequences are left over
-}

module Common.SimpPretty (

        -- * The document type
        SDoc,            -- Abstract

        -- * Primitive SDocuments
        empty, comma,

        -- * Converting values into documents
        text,

        -- * Wrapping documents in delimiters
        parens, brackets, braces,

        -- * Combining documents
        (<>), 

        -- * Rendering documents

        render, fullRender, writeFileSDoc
  ) where


import Prelude
import System.IO

infixl 6 <> 

-- ---------------------------------------------------------------------------
-- The interface

-- The primitive SDoc values

empty   :: SDoc;                        -- ^ An empty document
comma   :: SDoc;                 -- ^ A ',' character
text     :: String   -> SDoc

parens       :: SDoc -> SDoc;   -- ^ Wrap document in @(...)@
brackets     :: SDoc -> SDoc;   -- ^ Wrap document in @[...]@
braces       :: SDoc -> SDoc;           -- ^ Wrap document in @{...}@

-- Combining @SDoc@ values

(<>) :: SDoc -> SDoc -> SDoc;     -- ^Beside

-- Displaying @SDoc@ values. 

instance Show SDoc where
  showsPrec _prec doc cont = showSDoc doc cont

-- | Renders the document as a string using the default style
render     :: SDoc -> String

comma = text ","

parens p        = text "(" <> p <> text ")"
brackets p      = text "[" <> p <> text "]"
braces p        = text "{" <> p <> text "}"

-- ---------------------------------------------------------------------------
-- The SDoc data type

-- A SDoc represents a *set* of layouts.  A SDoc with
-- no occurrences of Union or NoSDoc represents just one layout.

-- | The abstract type of documents
data SDoc
 = Text String     -- text s
 | Beside SDoc SDoc                       

-- ---------------------------------------------------------------------------
-- @empty@, @text@

empty = Text ""
text = Text

-- ---------------------------------------------------------------------------
-- Horizontal composition @<>@

p <> q = Beside p q

-- ---------------------------------------------------------------------------
-- Displaying the best layout

writeFileSDoc :: FilePath -> SDoc -> IO ()
writeFileSDoc fp sd =
     do h <- openFile fp WriteMode
        fullRender (hPutStr h) (>>) sd
        hClose h

render doc       = showSDoc doc ""

showSDoc :: SDoc -> String -> String
showSDoc doc = fullRender showString (.) doc

fullRender :: (String -> a)
             -> (a -> a -> a)
             -> SDoc                    
             -> a                         
fullRender txt comp doc 
  = lay doc 
  where
    lay (Text s) = txt s 
    lay (Beside p q) = lay p `comp` lay q
