{- |
Module      :  $Header$
Copyright   :  (c) Sonja Groening, Christian Maeder, Uni Bremen 2004-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

utilities for the (Has)CASL, Haskell to Isabelle comorphisms

-}

-- possibly differentiate between HOL and HOLCF

module Isabelle.IsaConsts where

import Isabelle.IsaSign

-- * predefined sorts

holType :: Sort
holType = [IsaClass "hol_type"]

dom :: Sort
dom = [pcpo]

isaTerm :: IsaClass
isaTerm = IsaClass "type"

pcpo :: IsaClass
pcpo = IsaClass "pcpo"

-- * predefinded types

noType :: Typ
noType = Type "dummy" holType []

boolType :: Typ
boolType = Type "bool" holType []

mkOptionType :: Typ -> Typ
mkOptionType t = Type "option" holType [t]

prodType :: Typ -> Typ -> Typ
prodType t1 t2 = Type prodS holType [t1,t2]

mkFunType :: Typ -> Typ -> Typ
mkFunType s t = Type funS holType [s,t] -- was "-->" before

{-handy for multiple args: [T1,...,Tn]--->T  gives  T1-->(T2--> ... -->T)-}
mkCurryFunType :: [Typ] -> Typ -> Typ
mkCurryFunType = flip $ foldr mkFunType -- was "--->" before

voidDom :: Typ
voidDom = Type "void" dom []

{- should this be included (as primitive)? -}
flatDom :: Typ
flatDom = Type "flat" dom []

{- sort is ok? -}
mkContFun :: Typ -> Typ -> Typ
mkContFun t1 t2 = Type cFunS dom [t1,t2]

mkStrictProduct :: Typ -> Typ -> Typ
mkStrictProduct t1 t2 = Type sProdS dom [t1,t2]

mkContProduct :: Typ -> Typ -> Typ
mkContProduct t1 t2 = Type prodS dom [t1,t2]

{-handy for multiple args: [T1,...,Tn]--->T  gives  T1-->(T2--> ... -->T)-}
mkCurryContFun :: [Typ] -> Typ -> Typ
mkCurryContFun = flip $ foldr mkContFun -- was "--->" before

mkStrictSum :: Typ -> Typ -> Typ
mkStrictSum t1 t2 = Type sSumS dom [t1,t2]

prodS, sProdS, funS, cFunS, sSumS :: TName
prodS = "*"    -- this is printed as it is!
sProdS = "**"
funS = "=>"
cFunS = "->" 
sSumS = "++"

-- * functions for term formation

termAppl :: Term -> Term -> Term
termAppl t1 t2 = App t1 t2 NotCont

termMixfixAppl :: Term -> [Term] -> Term
termMixfixAppl t1 t2 = MixfixApp t1 t2 NotCont

-- | apply binary operation to arguments
--binConst :: String -> Term -> Term -> Term
--binConst s t1 t2 = termAppl (termAppl (conDouble s) t1) t2

binConst :: String -> Term -> Term -> Term
binConst s t1 t2 = MixfixApp (conDouble s) [t1,t2] NotCont

-- | construct a constant
conT :: VName -> Term
conT s = Const s noType

-- | construct a constant with no type
con :: VName -> Term
con s = Const s noType

mkVName :: String -> VName
mkVName s = VName { new = s, altSyn = "" }

conDouble :: String -> Term
conDouble = con . mkVName
	
-- * some stuff

someS :: String
someS = "Some"

conSomeT :: Typ -> Term
conSomeT t = Const (mkVName someS) t

-- | some constant with no type
conSome :: Term
conSome = conDouble someS

-- | defOp constant
defOp :: Term
defOp = conDouble"defOp"

-- | not constant
notOp :: Term
notOp = conDouble "Not"

-- * quantor strings

allS, exS, ex1S :: String
allS = "All"
exS = "Ex"
ex1S = "Ex1"

-- * strings of binary ops

cappl :: String
cappl = "op $"

conj :: String
conj = "op &"

disj :: String
disj = "op |"

impl :: String
impl = "op -->"

eq :: String
eq = "op ="

-- * binary junctors
binConj, binDisj, binImpl, binEqv, binEq :: Term -> Term -> Term
binConj = binConst conj
binDisj = binConst disj
binImpl = binConst impl
binEq = binConst eq
binEqv = binEq

-- * boolean constants
true, false :: Term
true = Const (mkVName "True") boolType
false = Const (mkVName "False") boolType

-- | pair stuff
pairC :: String
pairC = "pair"

isaPair :: String
isaPair = "Pair"
