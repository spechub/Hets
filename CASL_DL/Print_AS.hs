{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2005
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

pretty print AS of CASL_DL
-}

module CASL_DL.Print_AS where

import Common.Doc
import Common.DocUtils

import CASL.ToDoc ()
import CASL_DL.AS_CASL_DL

instance Pretty DL_FORMULA where
    pretty (Cardinality ct pn varTerm natTerm _) =
        text (case ct of
              CMin   -> minCardinalityS
              CMax   -> maxCardinalityS
              CExact -> cardinalityS)
        <> brackets (pretty pn)
        <> parens (pretty varTerm <> comma <+> pretty natTerm)
