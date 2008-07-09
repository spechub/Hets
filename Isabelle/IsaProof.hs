{- |
Module      :  $Header$
Copyright   :  (c) Andy Gimblett, Liam O'Reilly and Markus Roggenbach, Swansea University 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  provisional
Portability :  portable

Data structures for Isabelle Proofs
-}

module Isabelle.IsaProof where

data IsaProof = IsaProof
    { proof :: [ProofCommand],
      end :: ProofEnd
    } deriving (Show, Eq, Ord)

data ProofCommand
    = Apply ProofMethod
    | Back
    | Defer Int
    -- | Pr Int -- This proof command simply sets the number of
    -- goals shown in the display and is not needed
    | Prefer Int
    | Refute
      deriving (Show, Eq, Ord)

data ProofEnd
    = By ProofMethod
    | Done
    | Oops
    | Sorry
      deriving (Show, Eq, Ord)

data ProofMethod
    = Auto -- This is a plain auto with no parameters - it is used
           -- so often it warents its own constructor
    | Simp -- This is a plain auto with no parameters - it is used
           -- so often it warents its own constructor
    | Other String -- used for proof methods that have not been
                   -- implemented yet - including auto and simp
                   -- with parameters
      deriving (Show, Eq, Ord)
