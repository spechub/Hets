module GMPSAT where

--import
import qualified Data.Set as Set
import GMPAS
---------------------------------------------------------------------------------
-- SAT Decidability Algorithm
-- The folowing is a sketch of the algorithm and will need 
-- many other auxiliary things
---------------------------------------------------------------------------------
{-
checkSAT = do f <- par5er
           ; H <- guessPV f
           ; Ro = chooseCC H
           ; R = chooseRC Ro
           ; c = guessClause R
           ; res = checkSAT c R Ro
           ; return res
-}
----------------------------------------------------------------------------------
-- 1. Guess Pseudovaluation H for f
----------------------------------------------------------------------------------
guessPV :: (Ord t) => Formula t -> [Set.Set (TVandMA t)]
guessPV f =
    let l = genPV f
    in filter (eval f) l
-- modify the set of truth values / generate the next truth values set -----------
genTV :: (Ord t) => Set.Set (TVandMA t) -> Set.Set (TVandMA t)
genTV s =
    let
     (TVandMA (x,t),y) = Set.deleteFindMin s
    in if (t == False)
        then (Set.insert (TVandMA (x,True)) y)
        else if (y == Set.empty)
              then Set.empty
              else let
                    aux = genTV(y)
                    in if (aux == Set.empty)
                        then Set.empty
                        else (Set.insert (TVandMA (x,False)) aux)
-- generate a list with all Pseudovaluations of a formula ------------------------
genPV :: (Eq t, Ord t) => Formula t -> [Set.Set (TVandMA t)]
genPV f =
    let aux = setMA f
    in if (aux == Set.empty)
        then aux:[]
        else let recMakeList s =
                  let nextset = genTV s
                  in if (nextset == Set.empty)
                      then []
                      else (nextset:(recMakeList nextset))
             in (aux:(recMakeList aux))
-- Junctor evaluation -----------------------------------------------------------
jmap :: Junctor -> Bool -> Bool -> Bool
jmap j x y =
    case j of
        And -> and([x,y])
        Or -> or([x,y])
        If -> or([not(x),y])
        Fi -> or([x,not(y)])
        Iff -> and([or([not(x),y]),or([x,not(y)])])
-- Formula Evaluation with truth values provided by the TVandMA set -------------
eval :: (Eq a) => (Formula a) -> Set.Set (TVandMA a) -> Bool
eval f s =
    case f of
        T -> True
        F -> False
        Neg f1 -> not(eval f1 s)
        Junctor f1 j f2 -> (jmap j (eval f1 s) (eval f2 s))
        Mapp i f1 -> let findInS s ff =
                          if (s == Set.empty)
                            then False -- this could very well be True
                            else let (TVandMA (x,t),y) = Set.deleteFindMin s
                                 in if (x == ff)
                                     then t
                                     else findInS y ff
                     in
                        findInS s (Mapp i f1)
-- make (Truth Values, Modal Atoms) set from Formula f --------------------------
setMA :: (Ord t) => Formula t -> Set.Set (TVandMA t)
setMA f =
    case f of
        T -> Set.empty
        F -> Set.empty
        Neg f1 -> setMA f1
        Junctor f1 j f2 -> Set.union (setMA f1) (setMA f2)
        Mapp i f1 -> Set.insert (TVandMA (Mapp i f1,False)) Set.empty
---------------------------------------------------------------------------------
-- 2. Choose a contracted clause Ro /= F over MA(H) s.t. H "PL-entails" ~Ro
---------------------------------------------------------------------------------
{- For a pseudovaluation from the ones guessed to be pseudovaluations of H all 
the possible Ro such that H "entails" ~Ro will be generated (as a list) and put 
in a list themselves
-}
revTV s = if (s == Set.empty)
           then Set.empty
           else let (TVandMA (x,t),aux) = Set.deleteFindMin s
                in Set.insert (TVandMA (x,not(t))) (revTV aux)
nck s n k =
 case (n-k) of
  0 -> [revTV s]
  _ -> 
    case k of
     0 -> [Set.empty]
     _ -> let (TVandMA (x,t),aux) = Set.deleteFindMin s
          in (map (Set.insert (TVandMA (x,not(t)))) (nck aux (n-1) (k-1)))++
             (nck aux (n-1) k)
genAll s n = case n of
              0 -> []
              _ -> let size = Set.size s
                   in (nck s size n) ++ (genAll s (n-1))
test s = genAll s (Set.size s)
---------------------------------------------------------------------------------
-- 5. Recursively check that ~c(R,Ro) is satisfiable.
-- checkS
---------------------------------------------------------------------------------
