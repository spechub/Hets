{- |
Module      :  $Header$
Description :  Omega Lisp Output
Copyright   :  (c) Ewaryst Schulz, DFKI 2008
License     :  GPLv2 or higher

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  portable

The Lisp interface
-}
module Omega.ToLisp ( printLibrary ) where

import Data.List
import qualified Data.Map as Map

import Omega.DataTypes

data PrintEnvironment = Env { library::String, theory::String }

class SExprPrintable a where
  -- | Render instance to an SExpression string.
  toSExpr :: PrintEnvironment -> a -> String

emptyEnv :: PrintEnvironment
emptyEnv = Env "" ""


-- * THEORY HANDLING

theoremFun :: Bool -> String
theoremFun True = "theory:add-conjecture"
theoremFun False = "theory:add-axiom"

theoryFun :: String
theoryFun = "theory:add-theory"

symbolFun :: String
symbolFun = "theory:add-symbol"


-- | Outputs a library to omega's lisp format.
printLibrary :: Library -> String
printLibrary l = toSExpr emptyEnv l

instance SExprPrintable Library where
    toSExpr e (Library name theories) =
        let e' = e{library = name}
            in unlines $ map (toSExpr e') theories

instance SExprPrintable Theory where
    toSExpr e (Theory name imports items) =
        let e' = e{theory = name}
        in unlines $ toSExpr e' (theoryFun : show name : map show imports)
                               : map (toSExpr e') items

instance SExprPrintable TCElement where
    toSExpr e (TCAxiomOrTheorem isTheorem name formula) =
        toSExpr e [theoremFun isTheorem, show name, 
                   show $ printTerm formula, show $ theory e]
    toSExpr e (TCSymbol name) = toSExpr e [symbolFun, show name, show $ theory e]
--    toSExpr e (TCComment comment) = ""
    toSExpr _ _ = ""

instance SExprPrintable [String] where
    toSExpr _ l = "(" ++ intercalate " " l ++ ")"

-- * TERM HANDLING

data SymbolFormat = Infix | Other deriving (Show, Eq, Ord)

-- | Omegas built in symbols
symbolMap :: Map.Map String (Term, SymbolFormat)
symbolMap = Map.fromList [("__/\\__", (Symbol "/\\", Infix)),
                          ("__\\/__", (Symbol "\\/", Infix)),
                          ("__=>__", (Symbol "=>", Infix)),
                          ("__<=>__", (Symbol "<=>", Infix)),
                          ("__=__", (Symbol "=", Infix)),
                          ("not__", (Symbol "~", Other))]

symbolLookup :: Term -> Maybe (Term, SymbolFormat)
symbolLookup (Symbol name) = Map.lookup name symbolMap
symbolLookup _ = Nothing

printTerm :: Term -> String
printTerm (Symbol name) = name
printTerm (Var name) = name
printTerm (App _ []) =
    error "printTerm: application to zero arguments!"
printTerm (App fun args) =
    let mapped = symbolLookup fun
    in case mapped of
         Nothing -> concat [(printTerm fun), "(", concatSTL args, ")"]
         Just(t, Infix) -> concat ["(", printTerm (args!!0), " ",
                                   printTerm t, " ", printTerm (args!!1), ")"]
         Just(t, _) -> concat [(printTerm t), "(", concatSTL args, ")"]
printTerm (Bind binder vars body) =
    concat ["(", binder, " ", concatSTL vars, ". ", printTerm body, ")"]

concatSTL :: [Term] -> String
concatSTL l = intercalate "," (map printTerm l)
