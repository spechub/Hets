{- |

This folder contains the interface to the SoftFOL provers. Currently there are three prover interfaces available: SPASS, the MathServ Broker and Vampire whereas the latter is called via MathServ, too. The MathServ Broker chooses the best prover depending on the problem, as there are E, Otter, SPASS, Vampire.

The folder will be renamed to SoftFOL when the repository's version administrating system changes from CVS to Subversion.

The SPASS project homepage is located at <http://spass.mpi-sb.mpg.de/>.

"SPASS.Sign" provides data structures for SoftFOL signatures,
formulae and problems.

The emphasis is on outputting theories
with the pretty printer ("SPASS.Print"); hence, not only the
kernel language of SPASS is supported. Because the SPASS
logic is only used for proving, no parser and static analysis are provided.

"SPASS.Prove" is an interactive (SPASS is fully automated) interface to
the SPASS prover. It uses 'GUI.GenericATP.genericATPgui' for display
and interaction.

"SPASS.ProveMathServ" is similar to "SPASS.Prove" as it addresses the
MathServ Broker using the same GUI. The prover result (given by MathServ
response) will be parsed and mapped into 'GUI.GenericATPState.GenericConfig'
prover structures.

"SPASS.ProveVampire" is quite similar to "SPASS.ProveMathServ", using
MathServ for adressing the Vampire prover.

"SPASS.MathServParsing" provides functions for parsing a MathServ output into
a MathServResponse structure.

"SPASS.MathServMapping" maps a 'SPASS.MathServParsing.MathServResponse' into a
'GUI.GenericATPState.GenericConfig' structure.

"SPASS.ProverState" provides data structures and initialising functions for
Prover state and configurations.

"SPASS.ProveHelp" is a short help text when using SPASS interface.

"SPASS.Logic_SPASS" provides the SoftFOL instance of
type class 'Logic.Logic.Logic'.

"SPASS.ATC_SPASS": Automatic derivation of instances via DrIFT-rule Typeable, ShATermConvertible
  for the type(s): 'SPASS.Sign.Sign' 'SPASS.Sign.Generated' 'SPASS.Sign.SPProblem' 'SPASS.Sign.SPLogicalPart' 'SPASS.Sign.SPSymbolList' 'SPASS.Sign.SPSignSym' 'SPASS.Sign.SPDeclaration' 'SPASS.Sign.SPFormulaList' 'SPASS.Sign.SPOriginType' 'SPASS.Sign.SPTerm' 'SPASS.Sign.SPQuantSym' 'SPASS.Sign.SPSymbol' 'SPASS.Sign.SPDescription' 'SPASS.Sign.SPLogState' 'SPASS.Sign.SPSetting'

"SPASS.Conversions" provides functions to convert to internal SP\*
data structures.

"SPASS.CreateDFGDoc" prints a (G_theory CASL _) into a DFG Doc.

"SPASS.Translate" provides collection of functions used by "Comorphisms.CASL2SPASS" and all prover interfaces ("SPASS.Prove", "SPASS.ProveMathServ", "SPASS.ProveVampire") for the translation of CASL identifiers and axiom labels into valid SoftFOL identifiers.

"SPASS.Utils" are some utilities for SPASS and TPTP.

"SPASS.Print" arranges pretty printing for SoftFOL signatures in DFG syntax. Refer to <http://spass.mpi-sb.mpg.de/webspass/help/syntax/dfgsyntax.html> for the DFG syntax documentation.

"SPASS.PrintTPTP" arranges pretty printing for SoftFOL signatures in TPTP syntax. Refer to <http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html> for the TPTP syntax documentation.

Relevant papers on SPASS include:

C. Weidenbach, Spass: Combining superposition, sorts and splitting, in
Handbook of Automated Reasoning, A. Robinson and A. Voronkov, Eds. Elsevier,
1999.
-}

module SoftFOL where
