module GMPSAT where

import qualified Data.Set as Set
import GMPAS
import ModalLogic
-------------------------------------------------------------------------------
-- 1. Guess Pseudovaluation H for f                                  -- guessPV
-------------------------------------------------------------------------------
guessPV :: (Ord t) => Formula t -> [Set.Set (MATV t)]
guessPV f =
    let l = genPV f
        aux = filter (eval f) l
    in dropSVars aux
-- drop Variables from the Modal Atoms Set Lists ------------------------------
dropSVars :: (Ord t) => [Set.Set (MATV t)] -> [Set.Set (MATV t)]
dropSVars l =
    case l of
        []   -> []
        x:xs -> (dropVars x):(dropSVars xs)
-- drop Variables from a particular Set of Modal Atoms ------------------------
dropVars :: (Ord t) => Set.Set (MATV t) -> Set.Set (MATV t)
dropVars s = 
    if (s == Set.empty)
    then Set.empty
    else let (MATV (x,t),y) = Set.deleteFindMin s
             aux = dropVars y 
         in case x of
              Var _ _ -> aux
              _       -> Set.insert (MATV (x,t)) aux

-- modify the set of truth values / generate the next truth values set --------
genTV :: (Ord t) => Set.Set (MATV t) -> Set.Set (MATV t)
genTV s =
    let
     (MATV (x,t),y) = Set.deleteFindMin s
    in if (t == False)
       then (Set.insert (MATV (x,True)) y)
       else if (y == Set.empty)
            then Set.empty
            else let aux = genTV(y)
                 in if (aux == Set.empty)
                    then Set.empty
                    else (Set.insert (MATV (x,False)) aux)
-- generate a list with all Pseudovaluations of a formula ---------------------
genPV :: (Eq t, Ord t) => Formula t -> [Set.Set (MATV t)]
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
-- junctor evaluation ---------------------------------------------------------
jmap :: Junctor -> Bool -> Bool -> Bool
jmap j x y =
    case j of
        And -> and([x,y])
        Or -> or([x,y])
        If -> or([not(x),y])
        Fi -> or([x,not(y)])
        Iff -> and([or([not(x),y]),or([x,not(y)])])
-- formula evaluation with truth values provided by the MATV set --------------
eval :: (Eq a) => (Formula a) -> Set.Set (MATV a) -> Bool
eval f ts =
    let findInS s ff =
          if (s == Set.empty)
          then error "GMPSAT.eval"
          else let (MATV (x,t),y) = Set.deleteFindMin s
               in if (x == ff)
                  then t
                  else findInS y ff
    in case f of
        T               -> True
        F               -> False
        Neg f1          -> not(eval f1 ts)
        Junctor f1 j f2 -> (jmap j (eval f1 ts) (eval f2 ts))
        Mapp i f1       -> findInS ts (Mapp i f1)
        Var c i         -> findInS ts (Var c i) 
-- make (Truth Values, Modal Atoms) set from Formula f ------------------------
-- variables are treated as Modal Atoms ---------------------------------------
setMA :: (Ord t) => Formula t -> Set.Set (MATV t)
setMA f =
    case f of
        T -> Set.empty
        F -> Set.empty
        Neg f1 -> setMA f1
        Junctor f1 _ f2 -> Set.union (setMA f1) (setMA f2)
        Mapp i f1 -> Set.insert (MATV (Mapp i f1,False)) Set.empty
        Var x i -> Set.insert (MATV (Var x i,False)) Set.empty
-------------------------------------------------------------------------------
-- 2. Choose a ctr. cl. Ro /= F over MA(H) s.t. H "entails" ~Ro     -- roFromPV
-------------------------------------------------------------------------------
-- reverse the truth values of the set elements -------------------------------
revTV :: (Ord t, Eq t) => Set.Set (MATV t) -> Set.Set (MATV t)
revTV s = if (s == Set.empty)
          then Set.empty
          else let (MATV (x,t),aux) = Set.deleteFindMin s
               in Set.insert (MATV (x,not(t))) (revTV aux)
-- return the list of sets of n choose k of the set s -------------------------
nck :: (Ord t) => Set.Set (MATV t) -> Int -> Int -> [Set.Set (MATV t)]
nck s n k =
 case (n-k) of
  0 -> [revTV s]
  _ -> 
    case k of
     0 -> [Set.empty]
     _ -> let (MATV (x,t),aux) = Set.deleteFindMin s
          in (map (Set.insert (MATV (x,not(t)))) (nck aux (n-1) (k-1)))
             ++ (nck aux (n-1) k)
-- generate all unpermuted sets of size <= n of the set s ---------------------
--genAllSets :: (Ord t) => Set.Set (MATV t) -> Int -> [Set.Set (MATV t)]
genAllSets s n = 
    case n of
     0 -> []
     _ -> let size = Set.size s
          in (nck s size n) ++ (genAllSets s (n-1))
-- generates all ro lists from a given pseudovaluation ------------------------
--roFromPV :: (Ord t) => Set.Set (MATV t) -> [[MATV t]]
--roFromPV :: (Ord a) => Set.Set (MATV a) -> [RoClause a]
roFromPV s = let l = genAllSets s (Set.size s)
             in genAllLists l                          -- filter (not.null) ...
-- return the list of lists -> permutations of a set --------------------------
--perm :: (Ord t) => Set.Set t -> [[t]]
--perm :: (Ord t) => Set.Set t -> [RoClause t]
perm s = 
    if (Set.size s <= 1)
    then [Set.toList s]
    else let (x,aux1) = Set.deleteFindMin s
             (y,aux2) = Set.deleteFindMin aux1
         in map (x:) (perm aux1) ++ map (y:) (perm (Set.insert x aux2))
-- returns the input by transforming each set to list and permuting it --------
--genAllLists :: (Ord t) => [Set.Set t] -> [[t]]
--genAllLists :: (Ord t) => [Set.Set t] -> [RoClause t]
genAllLists l =
    case l of
     [] -> []                                                           -- [[]]
     _  -> (perm (head l)) ++ (genAllLists (tail l))
-- split the set-pseudovaluation depending on the pos/neg MAs -----------------
splitSet s =
    if (s == Set.empty)
    then (Set.empty,Set.empty)
    else let (MATV (x,t),aux) = Set.deleteFindMin s
             (a,b) = splitSet aux
         in if t 
            then (a, Set.insert (MATV (x,t)) b)
            else (Set.insert (MATV (x,t)) a, b)
--

-------------------------------------------------------------------------------
-- 5. Recursively check that ~c(R,Ro) is satisfiable.               -- checkSAT
-------------------------------------------------------------------------------
-- substitute the literals in a clause by the formulae under the modal atoms
-- and negates the resulted clause/formula
negSubst :: (Show a) => Clause -> [MATV a] -> Formula a
negSubst c ro =
  case c of
    Cl []            ->  
     case ro of 
       []                    -> T
       _                     -> error ("error @ GMPSAT.negSubst 1 "
                                ++ show c ++ " " ++ show ro)
    Cl (PLit _ : ll) ->
     case ro of
       MATV (Mapp _ ff,_):ml -> let g = negSubst (Cl ll) ml
                                in Junctor (Neg ff) And g
       _                     -> error ("error @ GMPSAT.negSubst 2 " 
                                ++ show c ++ " " ++ show ro)
    Cl (NLit _ : ll) ->
     case ro of
       MATV (Mapp _ ff,_):ml -> let g = negSubst (Cl ll) ml
                                in Junctor ff And g
       _                     -> error ("error @ GMPSAT.negSubst 3 " 
                                ++ show c ++ " " ++ show ro)
-- evaluate formula -----------------------------------------------------------
evalPF :: (Ord a, ModalLogic a b) => Formula a -> Bool
evalPF f =
    case f of
        T               -> True
        F               -> False
        Neg g           -> let e = evalPF g in not e 
        Junctor f1 j f2 -> let e1 = evalPF f1
                               e2 = evalPF f2
                           in jmap j e1 e2
        _               -> error "error @ GMPSAT.evalPF"
-------------------------------------------------------------------------------
-- TO BE DELETED. JUST FOR ORIENTATION ...
-- guessPV      -- generate all pseudovaluations of a formula
-- roFromPV     -- generate all rho from a given pseudovaluation
-- matchRO      -- match a rho against the rules of the logic
-- guessClause  -- guess a clause from the premise of the rules
-- negSubst     -- substitute underMA for literals and negate the result

-- guessPV :: (Ord t) => Formula t -> [Data.Set.Set (MATV t)]
-- roFromPV :: (Ord t) => Data.Set.Set (MATV t) -> [[MATV t]]
-- matchRO :: (ModalLogic a b) => [MATV a] -> [b]
-- guessClause :: (ModalLogic a b) => b -> [Clause]
-- negSubst :: Clause -> [MATV a] -> Formula a
-------------------------------------------------------------------------------
checksat :: (Show a, Ord a, ModalLogic a b) => Formula a -> Bool
checksat f = 
    any(\h->all(\ro->all(\mr->any(\cl->checksat(negSubst cl ro))
                        (guessClause mr))
               (matchRO ro))
       (roFromPV h))
    (guessPV f)
-- preprocess formula ---------------------------------------------------------
preprocess :: (ModalLogic a b) => Formula a -> Formula a
preprocess f = 
  let aux = flagML f 
  in case f of
        T                      -> T
        F                      -> F
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
ppCheckSAT :: (ModalLogic a b, Ord a, Show a) => Formula a -> Bool
ppCheckSAT f = let ff = preprocess f
               in checksat ff
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
