{- |
Module      :  $Header$
Description :  pretty printing combinators
Copyright   :  (c) Klaus Luettich, C. Maeder Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Pretty printing combinators

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

text :: String -> SDoc
text = Text

empty :: SDoc -- ^ An empty document
empty = text ""

comma :: SDoc -- ^ A ',' character
comma = text ","

parens :: SDoc -> SDoc -- ^ Wrap document in @(...)@
parens p = text "(" <> p <> text ")"

braces :: SDoc -> SDoc -- ^ Wrap document in @{...}@
braces p = text "{" <> p <> text "}"

brackets :: SDoc -> SDoc -- ^ Wrap document in @[...]@
brackets p = text "[" <> p <> text "]"

-- Horizontal composition @<>@
(<>) :: SDoc -> SDoc -> SDoc -- ^Beside
p <> q = Beside p q

-- Displaying @SDoc@ values.

instance Show SDoc where
  showsPrec = const showSDoc

-- | Renders the document as a string using the default style
render :: SDoc -> String
render doc = showSDoc doc ""

-- ---------------------------------------------------------------------------
-- The SDoc data type

-- | The abstract type of documents
data SDoc
 = Text String
 | Beside SDoc SDoc

-- ---------------------------------------------------------------------------
-- simple layout

writeFileSDoc :: FilePath -> SDoc -> IO ()
writeFileSDoc fp sd =
     do h <- openFile fp WriteMode
        fullRender (hPutStr h) (>>) sd
        hClose h

showSDoc :: SDoc -> String -> String
showSDoc = fullRender showString (.)

fullRender :: (String -> a) -> (a -> a -> a) -> SDoc -> a
fullRender txt comp doc
  = lay doc
  where
    lay (Text s) = txt s
    lay (Beside p q) = lay p `comp` lay q
