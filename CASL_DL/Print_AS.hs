{- |
Module      :  ./CASL_DL/Print_AS.hs
Copyright   :  (c) Klaus Luettich, Uni Bremen 2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

pretty print AS of CASL_DL
-}

module CASL_DL.Print_AS where

import Common.Doc
import Common.DocUtils

import CASL.ToDoc
import CASL_DL.AS_CASL_DL

instance FormExtension DL_FORMULA

instance Pretty DL_FORMULA where
    pretty (Cardinality ct pn varTerm natTerm qualTerm _) =
        text (show ct)
        <> brackets (pretty pn)
        <> parens (pretty varTerm <> comma <+> pretty natTerm
                   <> case qualTerm of
            Nothing -> empty
            Just x -> comma <+> pretty x)
