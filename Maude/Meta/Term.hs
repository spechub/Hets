module Maude.Meta.Term where

import Maude.Meta.Qid

import Data.Typeable (Typeable)

{-
*** types
  sorts Sort Kind Type .
  subsorts Sort Kind < Type < Qid .
-}

type Sort = Qid

data Type = Sort  Sort
          | Kind [Sort]
    deriving (Show, Eq, Ord, Typeable)


{-
*** terms
  sorts Constant Variable GroundTerm Term NeGroundTermList GroundTermList NeTermList TermList .
  subsorts Constant Variable < Qid Term .
  subsorts Constant < GroundTerm < Term NeGroundTermList < NeTermList .
  subsorts NeGroundTermList < NeTermList GroundTermList < TermList .
-}

data Term = Constant Qid Type   -- name, type; syntax: "<Qid>.<Type>"
          | Variable Qid Type   -- name, type; syntax: "<Qid>:<Type>"
          | Term     Qid TermList   -- operator, operands; syntax: "<Qid>[<TermList>]"
    deriving (Show, Eq, Ord, Typeable)

type TermList = [Term]


{-
*** substitutions
  sorts Assignment Substitution .
  subsort Assignment < Substitution .
-}

{-
*** contexts (terms with a single hole)
  sorts Context NeCTermList GTermList .
  subsort Context < NeCTermList < GTermList .
  subsorts TermList < GTermList .
-}