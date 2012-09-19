{- |
Module      :  $Header$
Description :  Interface to the Leo II theorem prover.
Copyright   :  (c) Jonathan von Schroeder, DFKI Bremen 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Jonathan von Schroeder <j.von_schroeder@dfki.de>
Stability   :  provisional
Portability :  non-portable

Leo II theorem prover for THF0
-}

module THF.ProveLeoII ( leoIIProver ) where

import THF.SZSProver
import Interfaces.GenericATPState
import Data.List (stripPrefix)
import Data.Maybe (fromMaybe)

pfun :: ProverFuncs
pfun = ProverFuncs {
 cfgTimeout = \ cfg -> maybe 601 (+1) (timeLimit cfg),
 proverCommand = \ _ tmpFile cfg ->
  let options = extraOpts cfg
      extraOptions = maybe "-po 1" (("-po 1 -t " ++) . show) (timeLimit cfg)
  in return ("leo",words extraOptions ++ [tmpFile]),
 getMessage = \ res' _ perr -> res' ++ perr,
 getTimeUsed = \ line ->
  case words (fromMaybe "" $ stripPrefix "# Total time" line) of
   _ : (tim : _) -> Just $ round $ (read tim :: Float) * 1000
   _ -> Nothing }

leoIIHelpText :: String
leoIIHelpText =
  "No help available yet.\n" ++
  "email hets-devel@informatik.uni-bremen.de " ++
  "for more information.\n"

leoIIProver :: ProverType
leoIIProver = createSZSProver "Leo II"
 leoIIHelpText pfun
