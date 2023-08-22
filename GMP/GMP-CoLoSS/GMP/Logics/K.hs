{- | Module     : ./GMP/GMP-CoLoSS/GMP/Logics/K.hs
 -  Description : Implementation of logic instance K
 -  Copyright   : (c) Daniel Hausmann & Georgel Calin & Lutz Schroeder, DFKI Lab Bremen,
 -                Rob Myers & Dirk Pattinson, Department of Computing, ICL
 -  License     : GPLv2 or higher, see LICENSE.txt
 -  Maintainer  : hausmann@dfki.de
 -  Stability   : provisional
 -  Portability : portable
 -
 - Provides the implementation of the matching functions the standard modal logic K.
 -}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}
module GMP.Logics.K where
import Data.List
import Data.Ratio
import Data.Maybe

import Debug.Trace
import Text.ParserCombinators.Parsec

import GMP.Logics.Generic
import GMP.Parser

{- ------------------------------------------------------------------------------
instance of feature K
------------------------------------------------------------------------------ -}

data K a = K [Formula a] deriving (Eq, Ord, Show)

{- For each positive modal literal, there is a premise containing only one
sequent. This sequent contains the stripped positive literal and all
negated stripped negative literals.
e.g. seq       = [ (M K p), !(M K q), (M K !p), !(M K !r)]
match seq = [ [[ p, !q, r]], [[ !p, !q, r]] ] -}

instance (SigFeature b c d, Eq (b (c d)), Eq (c d)) => NonEmptyFeature K b c d where
  nefMatch flags seq = let stripnlits = [ Neg (head phi) | (Neg (Mod (K phi))) <- seq]
                           striplits = [ head phi | Mod (K phi) <- seq]
                       in if flags !! 1
                          then trace ("\n  [K-matching this:] " ++ pretty_list seq)
                               [ [[Sequent (pos : stripnlits)]] | pos <- striplits]
                          else [ [[Sequent (pos : stripnlits)]] | pos <- striplits]

  nefPretty d = genfPretty d "[K]"
  nefFeatureFromSignature sig = K
  nefFeatureFromFormula phi = K
  nefStripFeature (K phis) = phis

{- ------------------------------------------------------------------------------
instance of sigFeature for K
------------------------------------------------------------------------------ -}

instance (SigFeature b c d, Eq (c d), Eq (b (c d))) => NonEmptySigFeature K b c d where
  neGoOn = genericPGoOn
