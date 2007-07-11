{-# OPTIONS -fglasgow-exts #-}
module ModalK where

import GMPAS
import ModalLogic
import qualified Data.Set as Set

data Krules = KR Int
    deriving Show

instance ModalLogic ModalK Krules where
    contrClause n ma = 
      let p = Set.difference ma n
      in [Implies (Set.toList p, [nn])|nn <- n]
    flagML _ = Sqr
    parseIndex = return (ModalK ())
    matchRO ro = if (rkn ro) 
                 then let Implies (n,_) = ro
                      in [KR (length n)] 
                 else []
    guessClause r = 
        case r of
            KR 0    -> [Cl [PLit 1]]
            KR n    -> let l = map NLit [1..n]
                           x = reverse l
                           c = reverse(PLit (n+1) : x)
                       in [Cl c]
                        
-- the RKn rule of the K modal logic ------------------------------------------
rkn :: RoClause ModalK -> Bool
rkn l =
    let Implies (_,p) = l
    in case p of
        [MATV (_,True)] -> True
        _               -> False
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
