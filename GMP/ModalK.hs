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
      in [Implies (Set.toList p, [nn])|nn <- Set.toList n]
    flagML _ = Sqr
    parseIndex = return (ModalK ())
    matchR (Implies (n,p)) =
      case p of
        [] -> []
        _  -> [KR (length n)] 
    guessClause r = 
        case r of
            KR 0    -> [Cl [PLit 1]]
            KR n    -> let l = map NLit [1..n]
                           x = reverse l
                           c = reverse(PLit (n+1) : x)
                       in [Cl c]
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
