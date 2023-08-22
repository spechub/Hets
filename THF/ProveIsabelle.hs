{- |
Module      :  ./THF/ProveIsabelle.hs
Description :  Interface to the Isabelle theorem prover.
Copyright   :  (c) Jonathan von Schroeder, DFKI Bremen 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Jonathan von Schroeder <jonathan.von_schroeder@dfki.de>
Stability   :  provisional
Portability :  non-portable

Isabelle theorem prover for THF0
-}

module THF.ProveIsabelle ( isaProver, nitpickProver,
                           refuteProver, sledgehammerProver ) where

import THF.SZSProver
import Interfaces.GenericATPState
import Data.List (isPrefixOf, stripPrefix)
import Data.Maybe (fromMaybe)

pfun :: String -> ProverFuncs
pfun tool = ProverFuncs {
 cfgTimeout = maybe 20 (+ 10) . timeLimit,
 proverCommand = \ tout tmpFile _ ->
  return ("time", ["isabelle", tool, show (tout - 10), tmpFile]),
 getMessage = \ res' pout _ ->
  if null res' then concat $ filter (isPrefixOf "*** ") (lines pout)
  else res',
 getTimeUsed = \ line -> case fromMaybe "" $ stripPrefix "real\t" line of
   [] -> Nothing
   s -> let sp p str = case dropWhile p str of
                  "" -> []
                  s' -> w : sp p s''
                   where (w, s'') = break p s'
            (m : secs : _) = sp (== 'm') s
        in Just $ read m * 60 + read secs }

createIsaSZSProver :: String -> String -> ProverFuncs -> ProverType
createIsaSZSProver = createSZSProver "isabelle"

isaProver :: ProverType
isaProver = createIsaSZSProver "Isabelle (automated)"
 "Automated Isabelle calling all tools available"
 $ pfun "tptp_isabelle_demo"

nitpickProver :: ProverType
nitpickProver = createIsaSZSProver "Isabelle (nitpick)"
 "Nitpick for TPTP problems"
 $ pfun "tptp_nitpick"

refuteProver :: ProverType
refuteProver = createIsaSZSProver "Isabelle (refute)"
 "refute for TPTP problems"
 $ pfun "tptp_refute"

sledgehammerProver :: ProverType
sledgehammerProver = createIsaSZSProver "Isabelle (sledgehammer)"
 "sledgehammer for TPTP problems"
 $ pfun "tptp_sledgehammer"
