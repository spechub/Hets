{- |
Module      :  $Header$
Description :  Omega Lisp Output
Copyright   :  (c) Ewaryst Schulz, DFKI 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  portable

The Lisp interface
-}
module Omega.ToLisp
    ( SExprPrintable(toSExpr) )
where

import Data.List

import Omega.DataTypes

class SExprPrintable a where
  -- | render instance to an SExpression string
  toSExpr :: a -> String

instance SExprPrintable Library where
    toSExpr (Library name theories) = ""

instance SExprPrintable Theory where
    toSExpr (Theory name imports items) = ""

instance SExprPrintable TCElement where
    toSExpr (TCAxiomOrTheorem isTheorem name formula) =
        toSExpr [showTheorem isTheorem,
                 show name, show $ printSimpleTerm formula]
    toSExpr (TCSymbol name) = toSExpr ["Symbol", show name]
    toSExpr (TCComment comment) = ""

instance SExprPrintable [String] where
    toSExpr l = "(" ++ intercalate " " l ++ ")"

showTheorem :: Bool -> String
showTheorem True = "Theorem"
showTheorem False = "Axiom"

printSimpleTerm :: Term -> String
printSimpleTerm (Symbol name) = name
printSimpleTerm (Var name) = name
printSimpleTerm (App fun []) =
    error "printSimpleTerm: application to zero arguments!"
printSimpleTerm (App fun args) =
    concat [(printSimpleTerm fun), "(", concatSTL args, ")"]
printSimpleTerm (Bind binder vars body) =
    concat [binder, " ", concatSTL vars, ". ", printSimpleTerm body]

concatSTL :: [Term] -> String
concatSTL l = intercalate "," (map printSimpleTerm l)

