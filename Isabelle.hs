{- |
Module      :  $Id$
Description :  logic for the interactive higher order theorem prover Isabelle
Copyright   :  (c) Christian Maeder, DFKI Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable (except Isabelle.Logic_Isabelle)

This folder contains the interface to the Isabelle theorem prover.

"Isabelle.IsaSign" provides data structures for Isabelle signatures,
formulas and theories. These resemble the ML data structures that
Isabelle uses. However, the emphasis is on outputting theories
with the pretty printer ("Isabelle.IsaPrint"); hence, not only the
kernel language of Isabelle is supported. Because the Isabelle
logic is only used for proving, no parser and static analysis are provided.

"Isabelle.IsaProve" is an interactive interface to the Isabelle prover.
"Isabelle.CreateTheories" is the batch version.

"Isabelle.Logic_Isabelle" provides the Isabelle instance of
type class 'Logic.Logic.Logic'.

"Isabelle.IsaConsts" and
"Isabelle.Translate" are auxiliary modules used in the comorphisms
into Isabelle, as well as in the prover module.
-}

module Isabelle where
