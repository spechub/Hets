module GMPSAT where

import qualified Data.Set as Set
import GMPAS
import ModalLogic
-------------------------------------------------------------------------------
-- SAT Decidability Algorithm
-- The folowing is a sketch of the algorithm and will need 
-- many other auxiliary things
-------------------------------------------------------------------------------
{-
checkSAT = do f <- par5er
           ; H <- guessPV f
           ; Ro = chooseCC H
           ; R = chooseRC Ro
           ; c = guessClause R
           ; res = checkSAT c R Ro
           ; return res
-}
-------------------------------------------------------------------------------
-- 1. Guess Pseudovaluation H for f                                    -- genPV
-------------------------------------------------------------------------------
guessPV :: (Ord t) => Formula t -> [Set.Set (TVandMA t)]
guessPV f =
    let l = genPV f
    in filter (eval f) l
-- modify the set of truth values / generate the next truth values set --------
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
-- generate a list with all Pseudovaluations of a formula ---------------------
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
-- Junctor evaluation ---------------------------------------------------------
jmap :: Junctor -> Bool -> Bool -> Bool
jmap j x y =
    case j of
        And -> and([x,y])
        Or -> or([x,y])
        If -> or([not(x),y])
        Fi -> or([x,not(y)])
        Iff -> and([or([not(x),y]),or([x,not(y)])])
-- Formula Evaluation with truth values provided by the TVandMA set -----------
eval :: (Eq a) => (Formula a) -> Set.Set (TVandMA a) -> Bool
eval f ts =
    case f of
        T -> True
        F -> False
        Neg f1 -> not(eval f1 ts)
        Junctor f1 j f2 -> (jmap j (eval f1 ts) (eval f2 ts))
        Mapp i f1 -> let findInS s ff =
                          if (s == Set.empty)
                            then False -- this could very well be True
                            else let (TVandMA (x,t),y) = Set.deleteFindMin s
                                 in if (x == ff)
                                     then t
                                     else findInS y ff
                     in
                        findInS ts (Mapp i f1)
-- make (Truth Values, Modal Atoms) set from Formula f ------------------------
setMA :: (Ord t) => Formula t -> Set.Set (TVandMA t)
setMA f =
    case f of
        T -> Set.empty
        F -> Set.empty
        Neg f1 -> setMA f1
        Junctor f1 _ f2 -> Set.union (setMA f1) (setMA f2)
        Mapp i f1 -> Set.insert (TVandMA (Mapp i f1,False)) Set.empty
-------------------------------------------------------------------------------
-- 2. Choose a ctr. cl. Ro /= F over MA(H) s.t. H "entails" ~Ro     -- ROfromPV
-------------------------------------------------------------------------------
-- reverse the truth values of the set elements -------------------------------
revTV :: (Ord t, Eq t) => Set.Set (TVandMA t) -> Set.Set (TVandMA t)
revTV s = if (s == Set.empty)
           then Set.empty
           else let (TVandMA (x,t),aux) = Set.deleteFindMin s
                in Set.insert (TVandMA (x,not(t))) (revTV aux)
-- return the list of sets of n choose k of the set s -------------------------
nck :: (Ord t) => Set.Set (TVandMA t) -> Int -> Int -> [Set.Set (TVandMA t)]
nck s n k =
 case (n-k) of
  0 -> [revTV s]
  _ -> 
    case k of
     0 -> [Set.empty]
     _ -> let (TVandMA (x,t),aux) = Set.deleteFindMin s
          in (map (Set.insert (TVandMA (x,not(t)))) (nck aux (n-1) (k-1)))
             ++ (nck aux (n-1) k)
-- generate all unpermuted sets of size <= n of the set s ---------------------
genAllSets :: (Ord t) => Set.Set (TVandMA t) -> Int -> [Set.Set (TVandMA t)]
genAllSets s n = 
    case n of
     0 -> []
     _ -> let size = Set.size s
          in (nck s size n) ++ (genAllSets s (n-1))
-- generates all ro lists from a given pseudovaluation ------------------------
roFromPV :: (Ord t) => Set.Set (TVandMA t) -> [[TVandMA t]]
roFromPV s = let l = genAllSets s (Set.size s)
             in genAllLists l
-- return the list of lists -> permutations of a set --------------------------
perm :: (Ord t) => Set.Set t -> [[t]]
perm s = 
    if (Set.size s <= 1)
     then [Set.toList s]
     else let (x,aux1) = Set.deleteFindMin s
              (y,aux2) = Set.deleteFindMin aux1
          in map (x:) (perm aux1) ++ map (y:) (perm (Set.insert x aux2))
-- returns the input by transforming each set to list and permuting it --------
genAllLists :: (Ord t) => [Set.Set t] -> [[t]]
genAllLists l =
    case l of
     [] -> []
     _  -> (perm (head l)) ++ (genAllLists (tail l))
-------------------------------------------------------------------------------
-- 5. Recursively check that ~c(R,Ro) is satisfiable.               -- checkSAT
-------------------------------------------------------------------------------
{-
subMAinG :: (Ord t) => (Clause, [TVandMA t]) -> [Formula t]
subMAinG(c,ro) = 
    case (c,ro) of
        (Cl [],[]) -> []
        (Cl (NLit _ : ls),(TVandMA (x,_)):xs) -> let Mapp _ f = x
                                                 in (Neg f):subMAinG(Cl ls,xs)
        (Cl (PLit _ : ls),(TVandMA (x,_)):xs) -> let Mapp _ f = x
                                                 in f:subMAinG(Cl ls,xs)
        (_,_) -> error "GMPSAT.subMAinG"

checkSAT f = let pv = genPV f
             in recCheck pv

recCheck pv =
    case pv of
        []   -> False
        x:xs -> if check x then True
                           else recCheck xs

check x = let lro = roFromPV x
          in mAndCheck lro

mAndCheck lro =
    case lro of
        []   -> False
        x:xs -> if roCheck x then True
                             else mAndCheck xs

roCheck ro = let lr = matchRO ro
             in listRec lr ro

listRec lr ro =
    case lr of
        []   -> False
        x:xs -> let c = head (guessClause x) -- this is incorrect
          -- recursion over the guessed clauses is needed as well
                    f = subMAinG(c,ro)
                in if evalML f then True
                               else listRec xs ro

evalML f =
    case f of
        T -> True
        F -> False
        Neg f1 -> not(evalML f1)
        Junctor f1 j f2 -> jmap j (evalML f1) (evalML f2)
        x -> checkSAT x
-}
