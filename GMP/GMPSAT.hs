module GMPSAT where

import qualified Data.Set as Set
import GMPAS
-- import ModalLogic
-------------------------------------------------------------------------------
-- 1. Guess Pseudovaluation H for f                                  -- guessPV 
-------------------------------------------------------------------------------
{- extract modal atoms from a given formula
 - @ param f : formula
 - @ return : list of modal atoms of f -}
extractMA :: Ord t => Formula t -> Set.Set (Formula t)
extractMA f = 
  case f of
    T             -> Set.empty
    F             -> Set.empty
    Neg g         -> extractMA g
    Junctor g _ h -> Set.union (extractMA g) (extractMA h)
    _             -> Set.singleton f
{- generate the powerset of a given set
 - @ param s : set
 - @ return : list of subsets of s -}
powerSet :: Ord t => Set.Set t -> [Set.Set t]
powerSet s = 
  if not (Set.null s)
  then let (e,r) = Set.deleteFindMin s
           aux = powerSet r
       in (map (Set.insert e) aux) ++ aux
  else [Set.empty]
{- evaluate pseudovaluation of formula
 - @ param f : formula
 - @ param p : the pseudovaluation, ie the positive modal atoms 
 - @ return : True if the pseudovaluation is good, False otherwise -}
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
{- drop variables from the pseudovaluations
 - @ param l : list of pseudovaluations
 - @ return : list of pseudovaluations in l without var items -}
dropLVars :: (Ord t) => [Set.Set (Formula t)] -> [Set.Set (Formula t)]
dropLVars l =
    case l of
        []   -> []
        x:xs -> (dropVars x):(dropLVars xs)
{- drop variables from a particular pseudovaluation
 - @ param s : pseudovaluation
 - @ return : pseudovaluation without var items -}
dropVars :: (Ord t) => Set.Set (Formula t) -> Set.Set (Formula t)
dropVars s = 
    if not (Set.null s)
    then let (x,y) = Set.deleteFindMin s
             aux = dropVars y 
         in case x of
              Var _ _ -> aux
              _       -> Set.insert x aux
    else Set.empty
{- generate all valid pseudovaluations out of a formula
 - @ param f : formula
 - @ param ma : list of modal atoms of f
 - @ return : list of valid pseudovaluations -}
guessPV :: Ord t => Formula t -> Set.Set (Formula t) -> [Set.Set (Formula t)]
guessPV f ma = let pv = powerSet ma
                   aux = filter (evalPV f) pv
               in dropLVars aux
-------------------------------------------------------------------------------
-- 2. Choose a ctr. cl. Ro /= F over MA(H) s.t. H "entails" ~Ro      -- ??
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------

