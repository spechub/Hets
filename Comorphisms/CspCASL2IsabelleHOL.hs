
{-

sublanguage of CASL: FinCommSubPCFOL= 
  signatures:
    finite set of sorts
    local top elements
       see CASL.Sublogic, add beyondCommSubPCFOL field to CASL_Sublogics
       adapt functions
         is_in_sign :: CASL -> CASL_Sublogics -> Sign () () -> Bool
             (you need to test only if beyondCommSubPCFOL==False)
         min_sublogic_sign :: CASL -> Sign () () -> CASL_Sublogics
             (test signature, set beyondCommSubPCFOL=False if test succeeds)
         proj_sublogic_sign :: CASL -> CASL_Sublogics -> Sign () () -> Sign () ()
             (if beyondCommSubPCFOL=False, then remove all components without top)
  signature morphisms:
    refl, non-ext
       adapt functions
         is_in_morphism :: CASL -> CASL_Sublogics -> Morphism () () () -> Bool
             (you need to test only if beyondCommSubPCFOL==False)
         min_sublogic_morphism :: CASL -> Morphism () () () -> CASL_Sublogics
             (test signature, set beyondCommSubPCFOL=False if test succeeds)
         proj_sublogic_morphism :: CASL -> CASL_Sublogics -> Morphism () () () -> Morphism () () ()
             (if beyondCommSubPCFOL=False, then remove all components without top)
  formulas are those of CASL (i.e. not all of FinCommSubPFOL= as in the paper)

translation FinCommSubPCFOL= to CASL (comorphism FinCommSubPCFOL2CASL)
  signature translation: 
    FinCommSubPFOL=-signature to CASL signature (construction of alphabet, see paper)
              see CASL.Sign, Data.Set, Data.Map, Common.Lib.Rel
       + axioms (see paper p. 28f.) for construction of quotient of sum of types
              see CASL.AS_BASIC_CASL.hs, datatype FORMULA
  sentence translation: identity

first step (hybrid system) comorphism CASL to IsabelleCspProver
   use FinCommSubPCFOL2CASL
   on the output, use CASL2PCFOL; PFCOL2CFOL; CASL2IsabelleHOL
   (code out subsorts, code out partiality, translate to Isabelle syntax)

   for the resulting Isabelle signature:
     chage "basesig" (see Isabelle.IsaSign) into "CspProver"

full step CspCASL -> Isabelle-CspProver
   signature translation : 
     use CASL2IsabelleCspProver
     translate process names into constants of process type
     channels? code them out before data construction
   formula translation
     process equation systems -> Isabelle
     (reusing CASL terms -> Isabelle
      + using CSP infrastructure of CSP-Prover)


refinement/views in CspCASL then state
  "each refinement of Sp1 is a refinement of Sp2"
  Csp-Prover should prove that this is equivalent to
  "Sp2 is a refinement of Sp1"
-}
