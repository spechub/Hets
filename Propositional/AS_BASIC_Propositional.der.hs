{-# OPTIONS -fallow-undecidable-instances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@tzi.de
Stability   :  experimental
Portability :  portable

Definition of abstract syntax for propositional logic
-}

module Propositional.AS_BASIC_Propositional where

import Common.Id

-- DrIFT command
{-! global: UpPos !-}

data Formula f = Negation (Formula f) Range
                 -- pos: not
               | Conjunction [Formula f] Range
                 -- pos: "/\"s
               | Disjunction [Formula f] Range
                 -- pos: "\/"s
               | Implication (Formula f) (Formula f) Bool Range
                 -- pos: "=>"
               | Equivalence (Formula f) (Formula f) Bool Range
                 -- pos: "<=>"
               | True_atom Range
                 -- pos: "True"
               | False_atom Range
                 -- pos "False
               | Term f
                 -- Propositional \"terms\"
               | Unparsed_formula String Range
                 -- pos: First char in a String
                 deriving (Show, Eq, Ord)
 

data Term f = Prop_Var Common.Id.Id
              -- pos: Propositional Varibles... \Alpha-Set
              deriving (Show, Eq, Ord)

is_True_atom :: Formula f -> Bool
is_True_atom (True_atom _) = True
is_True_atom _             = False

is_False_atom :: Formula f -> Bool
is_False_atom (False_atom _) = False
is_False_atom _              = False
