{- |
Module      :  $Id$
Description :  various encodings
Copyright   :  (c) Uni Bremen 2005-2007
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (existential types)

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

"Comorphisms.Prop2CASL"


On the other hand, there are a number of real encodings:

"Comorphisms.CASL2PCFOL", "Comorphisms.CASL2TopSort"  encodings of subsorting

"Comorphisms.CASL2SubCFOL" encoding of partiality

"Comorphisms.Sule2SoftFOL" translating a CASL subset to SoftFOL

"Comorphisms.Modal2CASL" encoding of Kripke worlds


"Comorphisms.HasCASL2Haskell"
  translation of executable HasCASL subset to Haskell

"Comorphisms.CspCASL2Modal"
  unfinished coding of CSP-CASL LTS semantics as Kripke models

"Comorphisms.CspCASL2IsabelleHOL"
  unfinished coding of CSP-CASL in IsabelleHOL

"Comorphisms.HasCASL2HasCASL"
  unfinished mapping of HasCASL subset to HasCASL program blocks


Finally, encodings to the theorem prover Isabelle:

"Comorphisms.CFOL2IsabelleHOL"

"Comorphisms.CoCFOL2IsabelleHOL"

"Comorphisms.PCoClTyCons2IsabelleHOL"
 unfinished translation of HasCASL subset to Isabelle

"Comorphisms.Haskell2IsabelleHOLCF"
-}

module Comorphisms where
