{- |
Module      :  $Header$
Copyright   :  (c) Sonja Groening, Christian Maeder, Uni Bremen 2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

utilities for the HasCASL to Isabelle comorphism
-}

module Isabelle.IsaConsts where

import Isabelle.IsaSign

-- | application
termAppl :: Term -> Term -> Term
termAppl t1 t2 = App t1 t2 NotCont

-- | apply binary operation to arguments
binConst :: String -> Term -> Term -> Term
binConst s t1 t2 = termAppl (termAppl (con s) t1) t2

-- | construct a constant
conT :: String -> Term
conT s = Const s noType

-- | construct a constant with no type
con :: String -> Term
con s = Const s noType

-- * some stuff

someS :: String
someS = "Some"

conSomeT :: Typ -> Term
conSomeT t = Const someS t

-- | some constant with no type
conSome :: Term
conSome = con someS

-- | defOp constant
defOp :: Term
defOp = con "defOp"

-- | not constant
notOp :: Term
notOp = con "Not"

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

eqv :: String
eqv = "op ="

eq :: String
eq = "op ="

-- * binary junctors
binConj, binDisj, binImpl, binEqv, binEq :: Term -> Term -> Term
binConj= binConst conj
binDisj = binConst disj
binImpl = binConst impl
binEq = binConst eq
binEqv = binConst eqv

-- * boolean constants
true, false :: Term
true = Const "True" boolType
false = Const "False" boolType

-- | pair stuff
pairC :: String
pairC = "pair"

isaPair :: String
isaPair = "Pair"
