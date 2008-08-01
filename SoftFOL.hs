{- |
Description :  logic for first order provers like SPASS

This folder contains the interface to the SoftFOL provers. Currently there are
three prover interfaces available: SPASS, the MathServ Broker and Vampire
whereas the latter is called via MathServ, too. The MathServ Broker chooses
the best prover depending on the problem, as there are E, Otter, SPASS,
Vampire.

The folder will be renamed to SoftFOL when the repository's version
administrating system changes from CVS to Subversion.

The SPASS project homepage is located at <http://spass.mpi-sb.mpg.de/>.

"SoftFOL.Sign" provides data structures for SoftFOL signatures,
formulae and problems.

The emphasis is on outputting theories
with the pretty printer ("SoftFOL.Print"); hence, not only the
kernel language of SPASS is supported. Because the SPASS
logic is only used for proving, no parser and static analysis are provided.

"SoftFOL.ProveSPASS" is an interactive (SPASS is fully automated) interface to
the SPASS prover. It uses 'GUI.GenericATP.genericATPgui' for display
and interaction.

"SoftFOL.ProveMathServ" is similar to "SoftFOL.ProveSPASS" as it addresses the
MathServ Broker using the same GUI. The prover result (given by MathServ
response) will be parsed and mapped into 'GUI.GenericATPState.GenericConfig'
prover structures.

"SoftFOL.ProveVampire" is quite similar to "SoftFOL.ProveMathServ", using
MathServ for adressing the Vampire prover.

"SoftFOL.MathServParsing" provides functions for parsing a MathServ output into
a MathServResponse structure.

"SoftFOL.MathServMapping" maps a 'SoftFOL.MathServParsing.MathServResponse'
into a 'GUI.GenericATPState.GenericConfig' structure.

"SoftFOL.ProverState" provides data structures and initialising functions for
Prover state and configurations.

"SoftFOL.Logic_SoftFOL" provides the SoftFOL instance of
type class 'Logic.Logic.Logic'.

"SoftFOL.ATC_SoftFOL": Automatic ATC derivation

"SoftFOL.Conversions" provides functions to convert to internal SP\*
data structures.

"SoftFOL.CreateDFGDoc" prints a (G_theory CASL _) into a DFG Doc.

"SoftFOL.Translate" provides collection of functions used by
"Comorphisms.SuleCFOL2SoftFOL" and all prover interfaces
("SoftFOL.ProveSPASS", "SoftFOL.ProveMathServ", "SoftFOL.ProveVampire",
"SoftFOL.ProveDarwin") for the translation of CASL identifiers and axiom
labels into valid SoftFOL identifiers.

"SoftFOL.Print" arranges pretty printing for SoftFOL signatures in DFG
syntax. Refer to
<http://spass.mpi-sb.mpg.de/webspass/help/syntax/dfgsyntax.html> for the DFG
syntax documentation.

"SoftFOL.PrintTPTP" arranges pretty printing for SoftFOL signatures in TPTP
syntax. Refer to <http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html> for the
TPTP syntax documentation.

Relevant papers on SPASS include:

C. Weidenbach, Spass: Combining superposition, sorts and splitting, in
Handbook of Automated Reasoning, A. Robinson and A. Voronkov, Eds. Elsevier,
1999.
-}

module SoftFOL where
