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
import ConstraintCASL.Print_AS()

import Common.PrettyPrint
import Common.DocUtils

instance PrintLaTeX ConstraintFORMULA where
    printLatex0 = toOldLatex


