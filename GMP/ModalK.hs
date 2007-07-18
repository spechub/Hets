{-# OPTIONS -fglasgow-exts #-}
module ModalK where

import GMPAS
import ModalLogic
import qualified Data.Set as Set

data Krules = KR Int
    deriving Show

instance ModalLogic ModalK Krules where
--    orderIns _ = True
    contrClause p ma = 
      let n = Set.difference ma p
      in [Mimplies [aux] (Set.toList p)|aux <- Set.toList n]
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
