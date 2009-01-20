{- |
Module      :  $Header$
Description :  interface to the CspCASLProver (Isabelle based) theorem prover
Copyright   :  (c) Liam O'Reilly and Markus Roggenbach, Swansea University 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  provisional
Portability :  portable

CspCASLProver allows interactive theorem proving on CspCASL
specifications. See CspCASL.hs for details on the specification
language CspCASL.

"CspCASLProver.CspCASLProver" is an interactive interface to the
Isabelle prover (instanisated with CspProver). The encoding of CspCASL
into IsabelleHOL requires the generation of several Isabelle theories
where only the final theory requires user interaction.
-}
module CspCASLProver where
