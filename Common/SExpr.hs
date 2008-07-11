{- |
Module      :  $Header$
Description :  S-Expressions as intermediate output format
Copyright   :  (c) E. Schulz, D. Dietrich, C. Maeder, DFKI 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

S-Expressions for the translation from HasCASL, CASL and VSE to OMDoc
-}

module Common.SExpr where

import Common.Doc

data SExpr = SSymbol String | SList [SExpr] deriving (Eq, Ord, Show)

prettySExpr :: SExpr -> Doc
prettySExpr sexpr = case sexpr of
  SSymbol s -> text s
  SList l -> parens . fsep $ map prettySExpr l
