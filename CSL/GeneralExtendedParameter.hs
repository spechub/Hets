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
     complement. Such sequences are represented by an ordered
     sequence of intervals.

     A sequence of intervals [a_i, b_i] is normalized when for all i
     b_i + 1 < a_{i+1}

     This implies that this sequence is
     1. nonoverlapping (I_i and I_j are disjoint for i/=j)
     2. noncontinuing (The union of I_i and I_{i+1} is not an interval)
     3. ordered (i<j => !x,y. x in I_i and y in I_j => x < y)
-}


module CSL.GeneralExtendedParameter where

import Data.List (intercalate)

import CSL.EPBasic
import CSL.TreePO
import CSL.AS_BASIC_CSL
import Common.Id (tokStr)

-- ----------------------------------------------------------------------
-- * Datatypes for efficient Extended Parameter comparison
-- ----------------------------------------------------------------------

swapCompare :: Ordering -> Ordering
swapCompare GT = LT
swapCompare LT = GT
swapCompare x = x

data ExtNumber = LeftInf | RightInf | Regular APInt deriving (Show, Eq)

instance Ord ExtNumber where
    compare a b | a == b = EQ
                | otherwise =
                    case (a, b) of
                      (LeftInf, _) -> LT
                      (RightInf, _) -> GT
                      (Regular i, Regular j) -> compare i j
                      _ -> swapCompare $ compare (b, a)

type BaseInterval = (ExtNumber, ExtNumber)

leftOpen:: APInt -> BaseInterval
leftOpen i = (LeftInf, Regular i)

rightOpen:: APInt -> BaseInterval
rightOpen i = (Regular i, RightInf)

between:: APInt -> APInt -> BaseInterval
between i j = (Regular i, Regular j)


-- All methods in the following presuppose normalized expressions

-- | Normalized generalized representation of an extended parameter constraint
type EPExp = [BaseInterval]

showBaseInterval :: String -> BaseInterval -> String
showBaseInterval _ (LeftInf, RightInf) = error "showBaseInterval: unconstrained expression"
showBaseInterval s (LeftInf, Regular i) = concat [s, " <= ", show i]
showBaseInterval s (Regular i, RightInf) = concat [s, " >= ", show i]
showBaseInterval s (Regular i, Regular j)
    | i == j = concat [s, " = ", show j]
    | otherwise = concat [show i, " <= ", s, " <= ", show j]
showBaseInterval _ ep = error $ "malformed expression: " ++ show ep

showEP :: (String, EPExp) -> String
showEP (s, ep) = intercalate " \\/ " $ map (showBaseInterval s) ep

toBoolRep :: String -> EPExp -> BoolRep
toBoolRep = error "TODO"


-- | Conversion function into the more efficient representation.
toEPExp :: EXTPARAM -> Maybe (String, EPExp)
toEPExp (EP t r i) =
    let l = case r of 
              "<=" -> [leftOpen i]
              "<" -> [leftOpen $ i-1]
              ">=" -> [rightOpen i]
              ">" -> [rightOpen $ i+1]
              "=" -> [between i i]
              "!=" -> [leftOpen $ i-1, rightOpen $ i+1]
              "-|" -> []
              _ -> error $ "toEPExp: unsupported relation: " ++ r
    in if null l then Nothing else Just (tokStr t, l)

-- ----------------------------------------------------------------------
-- * Extended Parameter comparison (subset-comparison)
-- ----------------------------------------------------------------------

leftOf :: BaseInterval -> BaseInterval -> Bool
leftOf (_,b) (_,d) = b <= d

compareBI :: BaseInterval -> BaseInterval -> EPCompare
compareBI i1@(a,b) i2@(c,d)
    | i1 == i2 = Comparable EQ
    | b < c or a > d = Incomparable Disjoint
    | a <= c = if b < d then Incomparable Overlap else Comparable GT
    | b <= d = Comparable LT
    | otherwise = Incomparable Overlap


compareBIEP :: BaseInterval -> EPExp -> EPCompare
compareBIEP _ [] = Comparable GT
compareBIEP i1 [i2] = compareBI i1 i2
compareBIEP i1 (i2:l) =
    case compareBI i1 i2 of
      Incomparable Disjoint ->
          if leftOf i1 i2 then Incomparable Disjoint else compareBIEP i1 l
      Incomparable Overlap -> Incomparable Overlap
      Comparable EQ -> Comparable LT -- l has here at least length one!
      Comparable LT -> Comparable LT
      Comparable GT -> case compareBIEP i1 l of
                         -- EQ and LT is here an impossible outcome
                         Comparable GT -> Comparable GT
                         _ -> Incomparable Overlap


-- | Compares two 'EPExp': They are uncompareable if they overlap or are disjoint.
compareEP :: EPExp -> EPExp -> EPCompare
compareEP [] [] =  Comparable EQ
compareEP _ [] =  Comparable GT
compareEP [] _ =  Comparable LT
compareEP ep1@(i1:l1) ep2@(i2:l2) =
    case compareBI i1 i2 of
      Comparable EQ -> case compareEP l1 l2 of
                         Incomparable
    i1 == i2 -> wenn compareEP l1 l2 disjoint dann overlap sonst ergebnis
    i1 > i2 -> wenn compareEP 
    



