{- | Module     : $Header$
 -  Description : Implementation of logic instance of disjoint union of features
 -  Copyright   : (c) Daniel Hausmann & Georgel Calin & Lutz Schroeder, DFKI Lab Bremen,
 -                Rob Myers & Dirk Pattinson, Department of Computing, ICL 
 -  License     : GPLv2 or higher
 -  Maintainer  : hausmann@dfki.de
 -  Stability   : provisional
 -  Portability : portable
 -
 - Provides the implementation of the matching functions of disjoint union of features.
 -}

module GMP.Logics.DisjUnion where
import List
import Ratio
import Maybe

import Debug.Trace
import Text.ParserCombinators.Parsec

import GMP.Logics.Generic
import GMP.Logics.K
import GMP.Parser

--------------------------------------------------------------------------------
-- instance of feature for Disjoint union of features
--------------------------------------------------------------------------------

data DisjUnion a b c = DisjUnion ((a c),(b c)) deriving (Eq, Ord, Show)

instance (Feature a (c (d e)), Feature b (c (d e)), Eq (a (c (d e))), Eq (b (c (d e))), SigFeature c d e, Eq (d e)) => 
                          NonEmptyFeature (DisjUnion a b) c d e where
  nefMatch flags seq = let fstposlits = [ (Mod p) | (Mod (DisjUnion (p,q))) <- seq ]
                           fstneglits = [ Neg (Mod p) | Neg (Mod (DisjUnion (p,q))) <- seq ]
                           sndposlits = [ (Mod q) | (Mod (DisjUnion (p,q))) <- seq ]
                           sndneglits = [ Neg (Mod q) | Neg (Mod (DisjUnion (p,q))) <- seq ]
                       in if (flags!!1)
                            then trace ("\n  [+-matching this:] " ++ (pretty_list seq)) $
                                 [[[Sequent (fstposlits ++ fstneglits)]]]++[[[Sequent (sndposlits ++ sndneglits)]]]  
                            else [[[Sequent (fstposlits ++ fstneglits)]]]++[[[Sequent (sndposlits ++ sndneglits)]]]  
  nefPretty d = case d of DisjUnion (p,q) -> "[DisjUnion](" ++ fPretty p ++ fPretty q ++ ")"
  nefDisj2Conj (Mod (DisjUnion (p,q))) = Mod (DisjUnion ((\(Mod phi) -> phi) (fDisj2Conj (Mod p)),
                                                         (\(Mod phi) -> phi) (fDisj2Conj (Mod q))))
  nefNegNorm (Mod (DisjUnion (p,q))) = Mod (DisjUnion ((\(Mod phi) -> phi) (fNegNorm (Mod p)),
                                                       (\(Mod phi) -> phi) (fNegNorm (Mod q))))
  nefFeatureFromSignature (DisjUnion (p,q)) = \phi -> (DisjUnion (((fFeatureFromSignature p) phi), ((fFeatureFromSignature q) phi))) 
  nefStripFeature (DisjUnion (p,q)) = fStripFeature p
  nefParser (DisjUnion (p,q)) = return (\(phi:psi:_) -> (DisjUnion (((fFeatureFromSignature p) [phi]), ((fFeatureFromSignature q) [psi]))))
  nefSeparator sig = "+"

--------------------------------------------------------------------------------
-- instance of sigFeature for disjoint union of features
--------------------------------------------------------------------------------

instance (Eq (b (c (d e))),  Eq (a (c (d e))), Feature b (c (d e)), Feature a (c (d e)),
          SigFeature c d e, Eq (d e)) => NonEmptySigFeature (DisjUnion a b) c d e where
  neGoOn sig flag = genericPGoOn sig flag

