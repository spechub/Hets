{- |
  Proofs in development graphs.
   Follows Sect. IV:4.4 of the CASL Reference Manual.
See also  /Heterogeneous
specification and the heterogeneous tool set/
(<http://www.informatik.uni-bremen.de/~till/papers/habil.ps>), section 5.6.

"Proofs.Proofs" contains data types for proofs

"Proofs.EdgeUtils" and "Proofs.StatusUtils" contain
utilities.

The proof calculus for development graphs is contained
in the following modules:

"Proofs.InferBasic" rule /basic inference/

"Proofs.Global" rules /global decomposition/, /global subsumption/

"Proofs.Local" rules /local decomposition/, /local subsumption/
(these are derived rules in the calculus)

"Proofs.Composition" various composition rules

"Proofs.HideTheoremShift" rule /Hide-Theorem-Shift/

"Proofs.TheoremHideShift" rule /Theorem-Hide-Shift/

The remaining rules have not been implemented yet.
-}

module Proofs where
