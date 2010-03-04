{- | Module     : $Header$
 -  Description : Implementation of logic instance Mon
 -  Copyright   : (c) Daniel Hausmann & Georgel Calin & Lutz Schroeder, DFKI Lab Bremen,
 -                Rob Myers & Dirk Pattinson, Department of Computing, ICL 
 -  License     : Similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
 -  Maintainer  : hausmann@dfki.de
 -  Stability   : provisional
 -  Portability : portable
 -
 - Provides the implementation of the matching functions monotonic modal logic.
 -}

module GMP.Logics.Mon where
import List
import Ratio
import Maybe

import Debug.Trace
import Text.ParserCombinators.Parsec

import GMP.Logics.Generic
import GMP.Parser

--------------------------------------------------------------------------------
-- instance of feature for Monotonic logic
--------------------------------------------------------------------------------

data Mon a = Mon [Formula a] deriving (Eq,Show)

-- For any combination of a positive and a negative literal, there is a premise
-- containing only one sequent. This sequent contains only one formula over the
-- stripped positive literal and the negated stripped negative literal.
-- e.g. seq       = [ (M Mon p), !(M Mon q), (M Mon !p), !(M Mon !r)]
--      match seq = [ [[ p, !q]], [[p, r]], [[ !p, !q]], [[ !p, r]] ]

instance (SigFeature b c d, Eq (b (c d)), Eq (c d)) => NonEmptyFeature Mon b c d where
  nefMatch flags seq = let stripnlits = [ Neg (head phi) | (Neg (Mod (Mon phi))) <- seq]
                           striplits = [ (head phi) | (Mod (Mon phi)) <- seq]
                       in if (flags!!1)
                         then
                           [ [[(Sequent [(Neg (And (Neg neg) (Neg pos)))])]] | neg <- stripnlits, pos <- striplits]
                         else
                           [ [[(Sequent [(Neg (And (Neg neg) (Neg pos)))])]] | neg <- stripnlits, pos <- striplits]

  nefPretty d = genfPretty d "[Mon]"
  nefFeatureFromSignature sig = Mon
  nefFeatureFromFormula phi = Mon
  nefStripFeature (Mon phis) = phis

--------------------------------------------------------------------------------
-- instance of sigFeature for Monotonic logic
--------------------------------------------------------------------------------

instance (SigFeature b c d, Eq (c d), Eq (b (c d))) => NonEmptySigFeature Mon b c d where
  neGoOn sig flag = genericPGoOn sig flag
