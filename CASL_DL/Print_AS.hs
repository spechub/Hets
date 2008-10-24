{- |
Module      :  $Header$
Copyright   :  (c) Klaus Luettich, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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
    pretty (Cardinality ct pn varTerm natTerm qualTerm _) =
        text (show ct)
        <> brackets (pretty pn)
        <> parens (pretty varTerm <> comma <+> pretty natTerm
        <> (case qualTerm of
            Nothing -> text ""
            Just  x -> comma <+> pretty x))
