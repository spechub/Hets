{- |
Module      :  $Header$
Description :  Interface to the CspCASLProver (Isabelle based) theorem prover
Copyright   :  (c) Liam O'Reilly and Markus Roggenbach, Swansea University 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  provisional
Portability :  portable

CspCASLProver allows interactive theorem proving on CspCASL
specifications. See CspCASL.hs for details on the specification
language CspCASL.

"CspCASLProver.Consts" conatins constants and related fucntions for
CspCASLProver.

"CspCASLProver.CspCASLProver" is an interactive interface to the
Isabelle prover (instanisated with CspProver). The encoding of CspCASL
into IsabelleHOL requires the generation of several Isabelle theories
where only the final theory requires user interaction.

"CspCASLProver.CspProverConsts" contains Isabelle abstract syntax constants for
CSP-Prover operations

"CspCASLProver.IsabelleUtils" contains utilities for CspCASLProver
related to Isabelle. The functions here typically manipulate Isabelle
signatures.

"CspCASLProver.TransProcesses" contains functions that implement CspCASLProver's
translation of processes from CspCASL to CspProver.

"CspCASLProver.Utils" contains utilities for CspCASLProver related to the actual construction of
Isabelle theories.
-}
module CspCASLProver where
