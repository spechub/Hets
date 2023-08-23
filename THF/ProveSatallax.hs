{- |
Module      :  ./THF/ProveSatallax.hs
Description :  Interface to the Satallax theorem prover.
Copyright   :  (c) Jonathan von Schroeder, DFKI Bremen 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Jonathan von Schroeder <jonathan.von_schroeder@dfki.de>
Stability   :  provisional
Portability :  non-portable

Satallax theorem prover for THF0
-}

module THF.ProveSatallax ( satallaxProver ) where

import THF.SZSProver
import Interfaces.GenericATPState
import Data.List (stripPrefix)
import Data.Maybe (fromMaybe)

pfun :: ProverFuncs
pfun = ProverFuncs {
 cfgTimeout = maybe 10 (+ 1) . timeLimit,
 proverCommand = \ tout tmpFile _ ->
  return ("time", ["satallax", "-t", show tout, tmpFile]),
 getMessage = \ res' _ _ -> res',
 getTimeUsed = \ line -> case fromMaybe "" $ stripPrefix "real\t" line of
   [] -> Nothing
   s -> let sp p str = case dropWhile p str of
                  "" -> []
                  s' -> w : sp p s''
                   where (w, s'') = break p s'
            (m : secs : _) = sp (== 'm') s
        in Just $ read m * 60 + read secs }

satallaxProver :: ProverType
satallaxProver = createSZSProver "satallax" "Satallax"
 ("Satallax is an automated theorem prover for higher-order logic."
 ++ " The particular form of higher-order logic supported by Satallax"
 ++ " is Church's simple type theory with extensionality and choice operators.")
 pfun
