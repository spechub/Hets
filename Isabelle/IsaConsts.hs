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

intType :: Typ
intType = Type "int" holType []

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

maxPrio :: Int
maxPrio = 1000

lowPrio :: Int
lowPrio = 10

isaEqPrio :: Int
isaEqPrio = 2 -- left assoc

termAppl :: Term -> Term -> Term
termAppl t1 t2 = MixfixApp t1 [t2] NotCont

termMixfixAppl :: Term -> [Term] -> Term
termMixfixAppl t1 t2 = MixfixApp t1 t2 NotCont

-- | apply binary operation to arguments
binConst :: String -> Term -> Term -> Term
binConst s t1 t2 = MixfixApp (conDouble s) [t1,t2] NotCont

-- | construct a constant with no type
con :: VName -> Term
con s = Const s noType

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
defOp = conDouble "defOp"

-- | not constant
notOp :: Term
notOp = con $ VName "Not" $ Just $ AltSyntax "~/ _" [40] 40

-- * quantor strings

allS, exS, ex1S :: String
allS = "ALL"
exS = "EX"
ex1S = "EX!"

-- * strings of binary ops

conj :: String
conj = "op &"

disj :: String
disj = "op |"

impl :: String
impl = "op -->"

eq :: String
eq = "op ="

conjV :: VName
conjV = VName conj $ Just $ AltSyntax "(_ &/ _)"   [36, 35] 35

disjV :: VName
disjV = VName disj $ Just $ AltSyntax "(_ |/ _)"   [31, 30] 30

implV :: VName
implV = VName impl $ Just $ AltSyntax "(_ -->/ _)" [26, 25] 25

eqV :: VName
eqV   = VName eq   $ Just $ AltSyntax "(_ =/ _)"   [50, 51] 50

plusS :: String
plusS = "op +"

minusS :: String
minusS = "op -"

timesS :: String
timesS = "op *"

consS :: String
consS = "Cons"

plusV :: VName 
plusV = VName plusS $ Just $ AltSyntax "(_ +/ _)"   [65, 66] 65

minusV :: VName 
minusV = VName minusS $ Just $ AltSyntax "(_ -/ _)" [65, 66] 65

timesV :: VName 
timesV = VName timesS $ Just $ AltSyntax "(_ */ _)" [70, 71] 70

consV :: VName
consV = VName consS $ Just $ AltSyntax "(_ #/ _)" [66, 65] 65

binVNameAppl :: VName -> Term -> Term -> Term
binVNameAppl v t1 t2 = MixfixApp (con v) [t1,t2] NotCont

-- * binary junctors
binConj, binDisj, binImpl, binEqv, binEq :: Term -> Term -> Term
binConj = binVNameAppl conjV
binDisj = binVNameAppl disjV
binImpl = binVNameAppl implV
binEq   = binVNameAppl eqV
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
