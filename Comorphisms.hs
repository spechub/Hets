{- |

This folder contains various comorphisms (implemented using
the type class 'Logic.Comorphism.Comorphism'), which are then
collected to a logic graph in "Comorphisms.LogicGraph".
The latter is based on the list of logics collected in  
"Comorphisms.LogicList".

The individual comorphisms are on the one hand trivial embeddings:

"Comorphisms.CASL2CoCASL"

"Comorphisms.CASL2CspCASL"

"Comorphisms.CASL2HasCASL"

"Comorphisms.CASL2Modal"

On the ohter hand, there are a number of real encodings:


"Comorphisms.CASL2PCFOL", "Comorphisms.CASL2TopSort"  encodings of subsorting

"Comorphisms.PCFOL2FOL" encoding of partiality

"Comorphisms.Modal2CASL" encoding of Kripke worlds


"Comorphisms.HasCASL2Haskell" translation of executable HasCASL subset to Haskell


"Comorphisms.CspCASL2Modal" unfinished coding of CSP-CASL LTS semantics as Kripke models

"Comorphisms.HasCASL2HasCASL" unfinished mapping of HasCASL subset to HsCASL program blocks


Finally, encodings to the theorem prover Isabelle:

"Comorphisms.CASL2IsabelleHOL"

"Comorphisms.CoCASL2IsabelleHOL"

"Comorphisms.HasCASL2IsabelleHOL"

"Comorphisms.Haskell2IsabelleHOLCF"

-}

module Comorphisms where
