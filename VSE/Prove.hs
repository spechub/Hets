{- |
Module      :  $Header$
Description :  Interface to the VSE prover
Copyright   :  (c) C. Maeder, DFKI 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  needs POSIX

call an adaption of VSE II to hets
-}

module VSE.Prove (vse) where

import Logic.Prover
import VSE.As
import VSE.Ana

vse :: Prover VSESign Sentence () ()
vse = mkProverTemplate "VSE" () prove

prove :: String -> Theory VSESign Sentence () -> IO [Proof_status ()]
prove str th = undefined
