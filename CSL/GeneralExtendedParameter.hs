{- |
Module      :  $Header$
Description :  Handling of extended parameters
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  portable

This module defines an ordering on extended parameters and other analysis tools.

Extended parameters may be based on one of the following
     relations:

>    =, <=, >=, !=, <, >, -|

     We work more generally (compared to CSL.ExtendedParameter) with a
     sequence of intervals which generalizes sets representable by
     the given relations and with the advantage that this
     representation is closed under union, intersection and
     complement. Such sequences could be represented by an ordered
     sequence of their borders, e.g.

>    <=1,=3, as [-oo,2,2,4,oo]

     This means, the set of x with @x<=1 \\/ x=3@ is represented by:
     @x in ]-oo,2[@ and @x not in [2,2]@ and @x in ]2,4[@ and @x not in [4,oo]@

 -}

module CSL.GeneralExtendedParameter where

import Data.List (intercalate)

import CSL.TreePO
import CSL.AS_BASIC_CSL
import Common.Id (tokStr)

-- ----------------------------------------------------------------------
-- * Datatypes for efficient Extended Parameter comparison
-- ----------------------------------------------------------------------


data BaseInterval = LOpen APInt | ROpen APInt | Between APInt APInt

-- | Normalized generalized representation of an extended parameter constraint
type EPExp = [BaseInterval]

showBaseInterval :: String -> BaseInterval -> String
showBaseInterval s (LOpen i) = concat ["-oo < ", s, " <= ", show i]
showBaseInterval s (ROpen i) = concat [show i, " <= ", s, " < oo"]
showBaseInterval s (Between i j)
    | i == j = concat [s, " = ", show j]
    | otherwise = concat [show i, " <= ", s, " <= ", show j]

showEP :: (String, EPExp) -> String
showEP (s, ep) = intercalate " /\\ " $ map (showBaseInterval s) ep


-- | Conversion function into the more efficient representation.
toEPExp :: EXTPARAM -> Maybe (String, EPExp)
toEPExp (EP t r i) =
    let l = case r of 
              "<=" -> [LOpen i]
              "<" -> [LOpen $ i-1]
              ">=" -> [ROpen i]
              ">" -> [ROpen $ i+1]
              "=" -> [Between i i]
              "!=" -> [LOpen $ i-1, ROpen $ i+1]
              "-|" -> []
              _ -> error $ "toEPExp: unsupported relation: " ++ r
    in if null l then Nothing else Just (tokStr t, l)

-- | Compares two 'EPExp': They are uncompareable if they overlap or are disjoint.
compareEP :: EPExp -> EPExp -> EPCompare
compareEP  = error "TODO: compareEP"



