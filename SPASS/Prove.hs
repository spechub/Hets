{- |
Module      :  $Header$
Copyright   :  (c) Rene Wagner, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rwagner@tzi.de
Stability   :  provisional
Portability :  needs POSIX

Interface for the SPASS theorem prover.
   See <http://spass.mpi-sb.mpg.de/> for details on SPASS.

-}

module SPASS.Prove where

import Logic.Prover
import SPASS.Sign
import SPASS.Print

import Common.AS_Annotation
import Common.PrettyPrint

import qualified Common.Lib.Map
import qualified Common.Lib.Set
import qualified Common.Lib.Rel

{- |
  Not yet implemented.
-}
spassProver :: Prover Sign Sentence ()
spassProver =
  Prover { prover_name = "SPASS",
           prover_sublogic = "SPASS",
           prove = spassProve
         }

spassProve :: String -> Theory Sign Sentence -> IO([Proof_status ()])
spassProve thName (Theory sig nSens) = return []
