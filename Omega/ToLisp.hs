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
module Omega.ToLisp ( printLibrary ) where

import Data.List

import Omega.DataTypes

data PrintEnvironment = Env { library::String, theory::String }

class SExprPrintable a where
  -- | render instance to an SExpression string
  toSExpr :: PrintEnvironment -> a -> String

emptyEnv :: PrintEnvironment
emptyEnv = Env "" ""

printLibrary :: Library -> String
printLibrary l = toSExpr emptyEnv l

instance SExprPrintable Library where
    toSExpr e (Library name theories) =
        let e' = e{library = name}
            in unlines $ map (toSExpr e') theories

instance SExprPrintable Theory where
    toSExpr e (Theory name imports items) =
        let e' = e{theory = name}
        in unlines $ toSExpr e' ["addTheory", show name]
               : toSExpr e' ("addImports" : show name :map show imports)
               : map (toSExpr e') items

instance SExprPrintable TCElement where
    toSExpr e (TCAxiomOrTheorem isTheorem name formula) =
        toSExpr e [theoremFun isTheorem, show name, 
                   show $ printSimpleTerm formula, show $ theory e]
    toSExpr e (TCSymbol name) = toSExpr e ["addSymbol", show name, show $ theory e]
--    toSExpr e (TCComment comment) = ""
    toSExpr _ _ = ""

instance SExprPrintable [String] where
    toSExpr _ l = "(" ++ intercalate " " l ++ ")"

theoremFun :: Bool -> String
theoremFun True = "addTheorem"
theoremFun False = "addAxiom"

infixSymbols :: [Term]
infixSymbols = map Symbol ["/\\", "=>", "<=>", "\\/", "="]

printSimpleTerm :: Term -> String
printSimpleTerm (Symbol name) = name
printSimpleTerm (Var name) = name
printSimpleTerm (App _ []) =
    error "printSimpleTerm: application to zero arguments!"
printSimpleTerm (App fun args) =
    if elem fun infixSymbols then
        concat ["(", printSimpleTerm (args!!0), " ", printSimpleTerm fun, " ",
                   printSimpleTerm (args!!1), ")"]
    else concat [(printSimpleTerm fun), "(", concatSTL args, ")"]
printSimpleTerm (Bind binder vars body) =
    concat ["(", binder, " ", concatSTL vars, ". ", printSimpleTerm body, ")"]

concatSTL :: [Term] -> String
concatSTL l = intercalate "," (map printSimpleTerm l)
