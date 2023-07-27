{-# LANGUAGE CPP, TypeFamilies, DeriveDataTypeable #-}

module PGIP.GraphQL.Result.Sentence where

import qualified PGIP.GraphQL.Result.Axiom as GraphQLResultAxiom
import qualified PGIP.GraphQL.Result.Conjecture as GraphQLResultConjecture

import Data.Data

data Sentence = Axiom GraphQLResultAxiom.Axiom
              | Conjecture GraphQLResultConjecture.Conjecture
                deriving (Show, Typeable, Data)
