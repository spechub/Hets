{- |
Module      :  $Header$
Copyright   :  (c) Florian Mossakowski, Uni Bremen 2006
License     :  GPLv2 or higher

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Abstract syntax for ConstraintCASL
  Only the formula syntax is specified
-}

module ConstraintCASL.AS_ConstraintCASL where

import Common.Id
import CASL.AS_Basic_CASL

type ConstraintCASLBasicSpec = BASIC_SPEC () () ConstraintFORMULA

type ConstraintCASLFORMULA = FORMULA ConstraintFORMULA

data ConstraintFORMULA = Implication_ConstraintFormula
                         ATOMCONJUNCTION ATOMCONJUNCTION
                       | Equivalence_ConstraintFormula
                         ATOMCONJUNCTION ATOMCONJUNCTION
                       | Axiom_ConstraintFormula ATOMCONJUNCTION
                         deriving (Eq, Ord, Show)

data RELATION = Empty_Relation | Equal_Relation | Id_Relation Id
              | Relation_Disjunction [RELATION] | Inverse_Relation RELATION
                deriving (Eq, Ord, Show)


data ATOMCONJUNCTION = Atom_Conjunction [ATOM]
                   deriving (Eq, Ord, Show)


data ATOM = Prefix_Atom RELATION [(ConstraintTERM)]
          | Infix_Atom (ConstraintTERM) RELATION (ConstraintTERM)
            deriving (Eq, Ord, Show)

data ConstraintTERM = Atomar_Term Id | Composite_Term Id [ConstraintTERM]
                      deriving (Eq, Ord, Show)

instance GetRange ConstraintFORMULA -- default is nullRange
