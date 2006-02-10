{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable

latex output of the abstract syntax
-}

module ConstraintCASL.LaTeX_AS where

import ConstraintCASL.AS_ConstraintCASL
import ConstraintCASL.Print_AS

import Common.Id
import Common.PrettyPrint (printText0)
import Common.PrintLaTeX
import Common.Lib.Pretty
import Common.Keywords
import Common.PPUtils
import Common.LaTeX_utils
import Common.LaTeX_AS_Annotation
import CASL.LaTeX_AS_Basic

instance PrintLaTeX ConstraintFORMULA where
    printLatex0 = printText0


