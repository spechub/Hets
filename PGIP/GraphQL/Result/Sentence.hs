{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.Sentence where

import PGIP.GraphQL.Result.Axiom
import PGIP.GraphQL.Result.Conjecture

import Data.Data

data Sentence = SenAxiom Axiom | SenConjecture Conjecture
                deriving (Show, Typeable, Data)
