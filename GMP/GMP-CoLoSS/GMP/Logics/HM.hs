{- | Module     : $Header$
 -  Description : Implementation of logic instance HML
 -  Copyright   : (c) Daniel Hausmann & Georgel Calin & Lutz Schroeder, DFKI Lab Bremen,
 -                Rob Myers & Dirk Pattinson, Department of Computing, ICL 
 -  License     : GPLv2 or higher
 -  Maintainer  : hausmann@dfki.de
 -  Stability   : provisional
 -  Portability : portable
 -
 - Provides the implementation of the matching functions of Henessy-Milner logic.
 -}

module GMP.Logics.HM where
import List
import Ratio
import Maybe

import Debug.Trace
import Text.ParserCombinators.Parsec

import GMP.Logics.Generic
import GMP.Parser

--------------------------------------------------------------------------------
-- instance of feature for Hennessy-Milner logic
--------------------------------------------------------------------------------

data HM a = HM Char [Formula a] deriving (Eq,Show)

-- For each positive modal literal, there is a premise containing only one
-- sequent. This sequent contains the stripped positive literal and all
-- negated stripped negative literals with the same index.
-- e.g. seq       = [ (M (HM a) p), !(M (HM b) q), (M (HM b) !p), !(M (HM a) !r)]
--      match seq = [ [[ p, r]], [[ !p, r]] ]

instance (SigFeature b c d, Eq (b (c d)), Eq (c d)) => NonEmptyFeature HM b c d where
  nefMatch flags seq = let stripnlits ind = [ Neg (head phi) | (Neg (Mod (HM ind phi))) <- seq]
                       in if (flags!!1)
                            then
                              trace ("\n  <HM-matching this:> " ++ (pretty_list seq)) $
                              [ [[(Sequent ((head phi):stripnlits ind))]] | (Mod (HM ind phi)) <- seq]
                            else
                              [ [[(Sequent ((head phi):stripnlits ind))]] | (Mod (HM ind phi)) <- seq]

  nefPretty d = case d of 
                  HM c [] -> "[HM]" ++ (show c) ++ "nothing contained"
                  HM c e -> "[HM]" ++ (show c) ++ (pretty (head e))
  nefFeatureFromSignature sig = HM 'a'
  nefFeatureFromFormula phi = HM 'a'
  nefStripFeature (HM a phis) = phis

  nefDisj2Conj (Mod (HM c phi)) = Mod ((HM c ([disj2conj (head phi)])))
  nefNegNorm (Mod (HM c phi)) = Mod ((HM c ([negNorm (head phi)])))

  nefParser sig = do c <- letter
                     return $ HM c
                <?> "Parser.parseHMindex"

--------------------------------------------------------------------------------
-- instance of sigFeature for Hennessy-Milner logic
--------------------------------------------------------------------------------

instance (SigFeature b c d, Eq (c d), Eq (b (c d))) => NonEmptySigFeature HM b c d where
  neGoOn sig flag = genericPGoOn sig flag

