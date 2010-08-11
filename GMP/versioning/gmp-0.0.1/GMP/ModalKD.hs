{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
{-# OPTIONS -fglasgow-exts #-}
module GMP.ModalKD where

import GMP.GMPAS
import GMP.ModalLogic
import qualified Data.Set as Set

data KDrules = KDPR Int
             | KDNR Int
    deriving Show
data Rchoice = P | N | O
    deriving Eq

instance ModalLogic ModalKD KDrules where
    contrClause n ma =
      let p = Set.difference ma n
      in [Mimplies (Set.toList p) [aux]|aux <- Set.toList n]
         ++ [Mimplies (Set.toList p) []]
    flagML _ = Sqr
    parseIndex = return (ModalKD ())
    matchR (Mimplies n p) =
      case p of
        [] -> if (n == []) then [] else [KDNR (length n)]
        _  -> [KDPR (length n)]
    guessClause r =
        case r of
            KDPR 0 -> [Pimplies [1] []]
            KDPR n -> [Pimplies [n+1] [1..n]]
            KDNR n -> [Pimplies [] [1..n]]
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
