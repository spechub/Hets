module GMPSAT where

import qualified Data.Set as Set
import GMPAS
-- import ModalLogic
-------------------------------------------------------------------------------
-- 1. Guess Pseudovaluation H for f                                  -- guessPV 
-------------------------------------------------------------------------------
-- extract modal atoms from a given formula -----------------------------------
extractMA :: Ord t => Formula t -> Set.Set (Formula t)
extractMA f = 
  case f of
    T             -> Set.empty
    F             -> Set.empty
    Neg g         -> extractMA g
    Junctor g _ h -> Set.union (extractMA g) (extractMA h)
    _             -> Set.singleton f
-- generate the powerset of a given set ---------------------------------------
powerSet :: Ord t => Set.Set t -> [Set.Set t]
powerSet s = 
  if (s /= Set.empty)
  then let (e,r) = Set.deleteFindMin s
           aux = powerSet r
       in (map (Set.insert e) aux) ++ aux
  else [Set.empty]
-- generate all valid pseudovaluations out of a formula -----------------------
guessPV :: Ord t => Formula t -> [Set.Set (Formula t)]
guessPV f = let ma = extractMA f
                pv = powerSet ma
            in filter (evalPV f) pv
-- evaluate pseudovaluation of formula ----------------------------------------
evalPV :: Ord t => Formula t -> Set.Set (Formula t) -> Bool
evalPV f p = 
  case f of
    T             -> True
    F             -> False
    Neg g         -> not (evalPV g p)
    Junctor g j h -> let jeval w x y =
                           case w of
                             And -> and [x,y]
                             Or  -> or [x,y]
                             If  -> or [not x,y]
                             Fi  -> or [x, not y]
                             Iff -> and [or [not x, y],or [x, not y]]
                     in jeval j (evalPV g p) (evalPV h p)
    _             -> if (Set.member f p) then True
                                         else False
-------------------------------------------------------------------------------

