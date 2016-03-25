{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./ConstraintCASL/AS_ConstraintCASL.hs
Copyright   :  (c) Florian Mossakowski, Uni Bremen 2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Abstract syntax for ConstraintCASL
  Only the formula syntax is specified
-}

module ConstraintCASL.AS_ConstraintCASL where

import Data.Data

import Common.Id

import CASL.AS_Basic_CASL

type ConstraintCASLBasicSpec = BASIC_SPEC () () ConstraintFORMULA

type ConstraintCASLFORMULA = FORMULA ConstraintFORMULA

data ConstraintFORMULA = Implication_ConstraintFormula
                         ATOMCONJUNCTION ATOMCONJUNCTION
                       | Equivalence_ConstraintFormula
                         ATOMCONJUNCTION ATOMCONJUNCTION
                       | Axiom_ConstraintFormula ATOMCONJUNCTION
                         deriving (Show, Eq, Ord, Typeable, Data)

data RELATION = Empty_Relation | Equal_Relation | Id_Relation Id
              | Relation_Disjunction [RELATION] | Inverse_Relation RELATION
                deriving (Show, Eq, Ord, Typeable, Data)


data ATOMCONJUNCTION = Atom_Conjunction [ATOM]
                   deriving (Show, Eq, Ord, Typeable, Data)


data ATOM = Prefix_Atom RELATION [ConstraintTERM]
          | Infix_Atom ConstraintTERM RELATION ConstraintTERM
            deriving (Show, Eq, Ord, Typeable, Data)

data ConstraintTERM = Atomar_Term Id | Composite_Term Id [ConstraintTERM]
                      deriving (Show, Eq, Ord, Typeable, Data)

instance GetRange ConstraintFORMULA -- default is nullRange
