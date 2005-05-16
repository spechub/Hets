{- |

This folder contains the interface to the SPASS theorem prover.

The SPASS project homepage is located at <http://spass.mpi-sb.mpg.de/>.

"SPASS.Sign" provides data structures for SPASS signatures,
formulae and problems.

The emphasis is on outputting theories
with the pretty printer ("SPASS.Print"); hence, not only the
kernel language of SPASS is supported. Because the SPASS
logic is only used for proving, no parser and static analysis are provided.

"SPASS.Prove" is a non-interactive (SPASS is fully automated) interface to
the SPASS prover.

"SPASS.Logic_SPASS" provides the SPASS instance of
type class 'Logic.Logic.Logic'.
-}

--TODO: reference relevant papers

module SPASS where
