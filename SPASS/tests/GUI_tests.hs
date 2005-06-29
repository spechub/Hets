
-- | some GUI tests to use from ghci
module GUI_tests where 

import Common.AS_Annotation
import Logic.Prover

import SPASS.Sign
import SPASS.Prove


term_x :: SPTerm 
term_x = SPSimpleTerm (SPCustomSymbol "x")

test1 = spassProveGUI "Foo" (Theory SPASS.Sign.emptySign 
      [NamedSen "Ax" True (SPQuantTerm SPForall [term_x] (SPComplexTerm SPEquiv [SPComplexTerm (SPCustomSymbol "P") [term_x],SPComplexTerm (SPCustomSymbol "Q") [term_x]])), 
       NamedSen "Go" False (SPQuantTerm SPForall [term_x] (SPComplexTerm SPImplies [SPComplexTerm (SPCustomSymbol "Q") [term_x],SPComplexTerm (SPCustomSymbol "P") [term_x] ]))])