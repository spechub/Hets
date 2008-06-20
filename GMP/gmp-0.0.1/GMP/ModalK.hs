{-# OPTIONS -fglasgow-exts #-}
module GMP.ModalK where

import GMP.GMPAS
import GMP.ModalLogic
import qualified Data.Set as Set

data Krules = KR Int
    deriving Show

instance ModalLogic ModalK Krules where
    contrClause p ma =
      let n = Set.difference ma p
      in [Mimplies (Set.toList p) [aux]|aux <- Set.toList n]
    flagML _ = Sqr
    parseIndex = return (ModalK ())
    matchR (Mimplies n p) =
      case p of
        [] -> []
        _  -> [KR (length n)]
    guessClause r =
        case r of
            KR 0    -> [Pimplies [1] []]
            KR n    -> [Pimplies [n+1] [1..n]]
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
