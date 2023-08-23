{- |
Module      :  ./TPTP/Prover/EProver/ProofParser.hs
Description :  Parses an EProver proof.
Copyright   :  (c) Eugen Kuksa University of Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  non-portable (imports Logic)
-}

module TPTP.Prover.EProver.ProofParser (parseTimeUsed) where

import Data.Char
import Data.List

-- Find the "CPU  Time" line and parse the time
parseTimeUsed :: [String] -> Int
parseTimeUsed = fst . foldl' checkLine (-1, False)
  where
    checkLine :: (Int, Bool) -> String -> (Int, Bool)
    checkLine (time, found) line =
      if found
      then (time, found)
      else if "CPU  Time" `isPrefixOf` dropWhile (`elem` "%# ") line
           then let time' = case takeWhile isDigit $ last (words line) of
                      ds@(_ : _) -> read ds
                      _ -> time
                in (time', found)
           else (time, found)
