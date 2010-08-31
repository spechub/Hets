{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
module GMP.GMPSAT where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe
import GMP.GMPAS
import GMP.ModalLogic

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
guessPV :: (Ord t, Show t) =>
                    Formula t -> Set.Set (Formula t) -> [Set.Set (Formula t)]
guessPV f ma = let pv = powerSet ma
                   aux = filter (evalPV f) pv
               in dropLVars aux
-------------------------------------------------------------------------------
-- 2. Choose a ctr. cl. Ro /= F over MA(H) s.t. H "entails" ~Ro  -- contrClause
-------------------------------------------------------------------------------
-- 3. Choose a rule matching the previous contracted clause           -- matchR
-------------------------------------------------------------------------------
-- 4. Guess a clause c from the premise of the matching rule     -- guessClause
-------------------------------------------------------------------------------
-- 5. Recursively check that ~c(R,Rho) is satisfiable               -- checkSAT
-------------------------------------------------------------------------------
{- substitute the clause literals with the formulae under the MAs and negate it
 - @ param c : clause guessed at Step 4
 - @ param ro : contracted clause from Step 2
 - @ return : the negated clause as described above -}
negSubst :: (Show a) => PropClause -> ModClause a -> Formula a
negSubst (Pimplies x1 x2) (Mimplies y1 y2) =
  let junction i l zm =
       case l of
         []  -> T
         h:t -> case Map.lookup h zm of
                  Just (Mapp _ f) -> if (i == 1)
                                     then Junctor (Neg f) And (junction i t zm)
                                     else Junctor f And (junction i t zm)
                  _ -> error "junction"
  in if (length x1 == length y2)&&(length x2 == length y1)
     then
       let q = Map.fromList (zip [1..] (y1++y2))
       in Junctor (junction (1::Integer) x1 q) And (junction (0::Integer) x2 q)
     else error "error @ GMPSAT.negSubst"

{- main recursive function
 - @ param f : formula to be checked for satisfiability
 - @ return : the answer to "Is the formula Satisfiable ?" -}
checksat :: (Show a, Ord a, ModalLogic a b) => Formula a -> Bool
checksat f =
  let ma = extractMA f
      mav = dropVars ma
  in any(\h -> all(\ro -> all(\mr -> any(\cl -> checksat(negSubst cl ro))
                             (guessClause mr))
                  (matchR ro))
        (contrClause h mav))
     (guessPV f ma)

{- auxiliary function to preprocess the formula depending on the ML flag
 - @ param f : formula to be preprocessed
 - @ return : processed formula -}
preprocess :: (ModalLogic a b) => Formula a -> Formula a
preprocess f =
  let aux = flagML f
  in case f of
        Neg ff                 -> Neg (preprocess ff)
        Junctor f1 j f2        -> Junctor (preprocess f1) j (preprocess f2)
        Mapp (Mop i Angle) ff  -> if (aux == Sqr)
                                    then Neg $ Mapp (Mop i Square) (Neg ff)
                                    else f
        Mapp (Mop i Square) ff -> if (aux == Ang)
                                    then Neg $ Mapp (Mop i Angle) (Neg ff)
                                    else f
        _                      -> f

-- preprocess formula and check satisfiability --------------------------------
{- function to preprocess formula and check satisfiability
 - @ param f : starting formula
 - @ return : same as "checksat" -}
checkSAT :: (ModalLogic a b, Ord a, Show a) => Formula a -> Bool
checkSAT f = let g = specificPreProcessing f
                 h = if (isNothing g)
                     then error "GMPSAT.checkSAT: Ill-formed formula"
                     else preprocess (fromJust g)
             in checksat h
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
