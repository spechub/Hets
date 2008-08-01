{- |
Module      :  $Header$
Copyright   :  (c) Andy Gimblett, Liam O'Reilly and Markus Roggenbach,
                   Swansea University 2008
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
    | Using [String]
    | Back
    | Defer Int
    | Prefer Int
    | Refute
      deriving (Show, Eq, Ord)

data ProofEnd
    = By ProofMethod
    | DotDot
    | Done
    | Oops
    | Sorry
      deriving (Show, Eq, Ord)

data ProofMethod
    -- | This is a plain auto with no parameters - it is used
    --   so often it warents its own constructor
    = Auto
    -- | This is a plain auto with no parameters - it is used
    --   so often it warents its own constructor
    | Simp
    -- | Induction proof method. This performs induction upon a variable
    | Induct String
    -- |  Case_tac proof method. This perfom a case distinction on a term
    | CaseTac String
    -- | Subgoal_tac proof method . Adds a term to the local
    --   assumptions and also creates a sub-goal of this term
    | SubgoalTac String
    -- | Insert proof method. Inserts a lemma or theorem name to the assumptions
    --   of the first goal
    | Insert String
    -- | Used for proof methods that have not been implemented yet.
    --   This includes auto and simp with parameters
    | Other String
      deriving (Show, Eq, Ord)

toIsaProof :: ProofEnd -> IsaProof
toIsaProof e = IsaProof [] e

mkOops :: IsaProof
mkOops = toIsaProof Oops
