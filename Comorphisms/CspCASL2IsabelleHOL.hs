
{-
signature translation : CspCASL -> Isabelle-CspProver


resulting Isabelle signature:
  basesig = "CspProver"
  types + operations: 
     coding of the CASL part
     + construction of quotient of sum of types

formula translation
  process equation systems -> Isabelle
  (reusing CASL terms -> Isabelle
   + using CSP infrastructure of CSP-Prover)
  process equation systems should be coded to hold only "up to refinement"
  (cf. definition of CspCASL institution)

  refinement/views in CspCASL then state
  "each refinement of Sp1 is a refinement of Sp2"
  Csp-Prover should prove that this is equivalent to
  "Sp2 is a refinement of Sp1"
-}
