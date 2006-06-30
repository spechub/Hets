{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Christian Maeder, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

This module contains all instances of PrintLaTeX for AS_Annotation.hs
-}

module Common.LaTeX_AS_Annotation
    ( fromLatex
    ) where

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.PrettyPrint
import Common.Doc
import Common.DocUtils

instance PrintLaTeX Annotation where
    printLatex0 ga = toLatex ga . annoDoc

fromLatex :: PrintLaTeX a => GlobalAnnos -> a -> Doc
fromLatex ga = literalDoc . printLatex0 ga

instance PrintLaTeX a => PrintLaTeX (Annoted a) where
    printLatex0 ga = toLatex ga . printAnnoted (fromLatex ga)

instance PrintLaTeX s => PrintLaTeX (Named s) where
    printLatex0 ga = printLatex0 ga . fromLabelledSen
