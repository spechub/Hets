module PGIP.Common where

import Proofs.AbstractState

data ProverOrConsChecker = Prover G_prover
                         | ConsChecker G_cons_checker
                         deriving (Show)
