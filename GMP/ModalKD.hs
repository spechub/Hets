{-# OPTIONS -fglasgow-exts #-}
module ModalKD where

import GMPAS
import ModalLogic
import qualified Data.Set as Set

data KDrules = KDPR Int
             | KDNR Int
    deriving Show
data Rchoice = P | N | O
    deriving Eq

instance ModalLogic ModalKD KDrules where
    orderIns _ = True
    contrClause n ma =
      let p = Set.difference ma n
      in [Implies (Set.toList p, [nn])|nn <- Set.toList n] ++
         [Implies (Set.toList p, [])]
    flagML _ = Sqr
    parseIndex = return (ModalKD ())
    matchR (Implies (n,p)) = 
      case p of
        [] -> if (n == []) then []
                           else [KDNR (length n)]
        _  -> [KDPR (length n)]
    guessClause r = 
        case r of
            KDPR 0 -> [Cl [PLit 1]]
            KDPR n -> let l = map NLit [1..n]
                          x = reverse l
                          c = reverse(PLit (n+1) : x)
                      in [Cl c]
            KDNR n -> let c = map NLit [1..n]
                      in [Cl c]
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
