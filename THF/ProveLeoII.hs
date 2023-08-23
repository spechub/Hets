{- |
Module      :  ./THF/ProveLeoII.hs
Description :  Interface to the Leo II theorem prover.
Copyright   :  (c) Jonathan von Schroeder, DFKI Bremen 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Jonathan von Schroeder <jonathan.von_schroeder@dfki.de>
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
 cfgTimeout = maybe 601 (+ 20) . timeLimit,
 proverCommand = \ tout tmpFile _ ->
  let extraOptions = ("-po 0 -t " ++) . show $ tout
  in return ("leo", words extraOptions ++ [tmpFile]),
 getMessage = \ res' _ perr -> let msg = res' ++ perr
                               in if not $ null msg then msg
                                  else unlines
                                   ["Leo seem to have terminated early.",
                                    "Probably increasing the timelimit",
                                    "will help." ],
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
leoIIProver = createSZSProver "leo" "Leo II"
 leoIIHelpText pfun
