{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@tzi.de
Stability   :  provisional
Portability :  unknown

Pretty printing for OWL DL theories.

-}

{-
    todo:
     - invent ASCII display syntax for OWL_DL theories (Klaus)
     - implement printing of a theory
-}

module OWL_DL.Print where

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Lib.Pretty
import Common.PrettyPrint

import OWL_DL.Sign
import OWL_DL.AS

instance PrintLaTeX Sign where
  printLatex0 = printText0

instance PrettyPrint Sign where
  printText0 _ = text . show

instance PrintLaTeX Sentence where
  printLatex0 = printText0

instance PrettyPrint Sentence where
 printText0 _ = text . show

instance PrettyPrint Ontology where
 printText0 _ = text. show

instance PrintLaTeX Ontology where
 printLatex0 = printText0

