{- | Module     : $Header$
 -  Description : Implementation of logic instance KD
 -  Copyright   : (c) Daniel Hausmann & Georgel Calin & Lutz Schroeder, DFKI Lab Bremen,
 -                Rob Myers & Dirk Pattinson, Department of Computing, ICL 
 -  License     : Similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
 -  Maintainer  : hausmann@dfki.de
 -  Stability   : provisional
 -  Portability : portable
 -
 - Provides the implementation of the matching functions the modal logic KD.
 -}

module GMP.Logics.KD where
import List
import Ratio
import Maybe

import Debug.Trace
import Text.ParserCombinators.Parsec

import GMP.Logics.Generic
import GMP.Parser

--------------------------------------------------------------------------------
-- instance of feature KD
--------------------------------------------------------------------------------

data KD a = KD [Formula a] deriving (Eq, Ord, Show)

-- For each positive modal literal, there is a premise containing only one
-- sequent. This sequent contains the stripped positive literal and all
-- negated stripped negative literals. Also there is an additional premise,
-- containing the sequent of all negated stripped negative literals.
-- e.g. seq       = [ (M KD p), !(M KD q), (M KD !p), !(M KD !r)]
--      match seq = [ [[ p, !q, r]], [[ !p, !q, r]], [[!q, r]] ]

instance (SigFeature b c d, Eq (b (c d)), Eq (c d)) => NonEmptyFeature KD b c d where
  nefMatch flags seq = let stripnlits = [ Neg (head phi) | (Neg (Mod (KD phi))) <- seq]
                           striplits = [ (head phi) | (Mod (KD phi)) <- seq]
                       in if (flags!!1)
                            then trace ("\n  <KD-matching this:> " ++ (pretty_list seq)) $
                                 [ [[(Sequent (pos:stripnlits))]] | pos <- striplits] ++
                                   [[[ (Sequent stripnlits) ]]]
                            else [ [[(Sequent (pos:stripnlits))]] | pos <- striplits] ++
                                   [[[ (Sequent stripnlits) ]]]


  nefPretty d = genfPretty d "[KD]"
  nefFeatureFromSignature sig = KD
  nefFeatureFromFormula phi = KD
  nefStripFeature (KD phis) = phis

--------------------------------------------------------------------------------
-- instance of sigFeature for KD
--------------------------------------------------------------------------------

instance (SigFeature b c d, Eq (c d), Eq (b (c d))) => NonEmptySigFeature KD b c d where
  neGoOn sig flag = genericPGoOn sig flag
