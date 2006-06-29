{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

LaTeX Pretty Printing heterogenous
   libraries in HetCASL.
-}

module Syntax.LaTeX_AS_Library() where

import Common.Keywords
import Common.DocUtils
import Common.PrettyPrint
import Common.Id
import Syntax.AS_Library

import Syntax.Print_AS_Library

instance PrintLaTeX LIB_DEFN where
    printLatex0 = toOldLatex

instance PrintLaTeX LIB_ITEM where
    printLatex0 = toOldLatex

instance PrintLaTeX ITEM_NAME_OR_MAP where
    printLatex0 = toOldLatex

instance PrintLaTeX LIB_NAME where
    printLatex0 = toOldLatex

instance PrintLaTeX LIB_ID where
    printLatex0 = toOldLatex

instance PrintLaTeX VERSION_NUMBER where
    printLatex0 = toOldLatex
