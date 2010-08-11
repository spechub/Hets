{- |
Module      :  $Header$
Description :  A formula wrapper from formulae defined in SoftFOL.Sign to data Formula defined in Common.Normalization
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  GPLv2 or higher

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
module Search.SPASS.FormulaWrapper where


import Search.Common.Data
import SoftFOL.Sign

type SpassConst = SPIdentifier 

wrapTerm :: SPTerm -> Formula (Constant SpassConst) SPIdentifier
wrapTerm (SPQuantTerm q vars f) = Binder (wrapQConst q) (map wrapVar vars) (wrapTerm f)
wrapTerm (SPComplexTerm SPImplied args) = wrapTerm (SPComplexTerm SPImplies (reverse args)) -- ist das die Semantik von implied?!?
wrapTerm (SPComplexTerm f args) = 
    case f
    of (SPCustomSymbol s) -> Var s (map wrapTerm args)
       _ -> Const (wrapConst f) (map wrapTerm args)
wrapTerm (SPSimpleTerm c) = 
    case c
    of (SPCustomSymbol s) -> Var s []
       _ -> Const (wrapConst c) []

wrapConst :: SPSymbol -> Constant SpassConst
wrapConst SPEqual = Equal
wrapConst SPTrue = TrueAtom
wrapConst SPFalse = FalseAtom
wrapConst SPOr = Or
wrapConst SPAnd = And
wrapConst SPNot = Not
wrapConst SPImplies = Imp
wrapConst SPEquiv = Eqv
--wrapConst SPXor = Xor

wrapQConst :: SPQuantSym -> Constant SpassConst
wrapQConst SPForall = All
wrapQConst SPExists = Some
wrapQConst (SPCustomQuantSym q) = LogicDependent q

wrapVar :: SPTerm -> SPIdentifier
wrapVar (SPSimpleTerm (SPCustomSymbol v)) = v -- only single variable can be bound
wrapVar v = error (show v ++ " is not allowed as bound variable")
