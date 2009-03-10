{- | Module     : $Header$
 -  Description : Implementation of logic instances
 -  Copyright   : (c) Daniel Hausmann & Georgel Calin & Lutz Schroeder, DFKI Lab Bremen,
 -                Rob Myers & Dirk Pattinson, Department of Computing, ICL 
 -  License     : Similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
 -  Maintainer  : hausmann@dfki.de
 -  Stability   : provisional
 -  Portability : portable
 -
 - Provides the implementation of the matching functions for several logics.
 - Currently implemented: K, KD, Mon, HM, C, P, G
 -}

module GMP.Logics where
import List
import Ratio
import Maybe

import Debug.Trace

import GMP.IneqSolver
import GMP.Generic
import GMP.Prover

--------------------------------------------------------------------------------
-- generic functions for containers of formulae
--------------------------------------------------------------------------------

-- expand applies all sequent rules that do not induce branching
normalize :: (Logic a) => L a -> L a
normalize (Neg (Neg phi)) = normalize phi
normalize (Neg phi) = Neg (normalize phi)
normalize (And phi psi) = And (normalize phi) (normalize psi)
normalize (M mod xs) = M mod (map normalize xs)
normalize x = x

first :: (a,b) -> a
first (p,q) = p

second :: (a,b) -> b
second (p,q) = q

pair :: (a->b) -> (c->d) -> (a,c) -> (b,d)
pair f g (p,q) =  (f(p),g(q))

-- Strip any modal operator from all positive occurences. Remove all other formulae
strip_any_literals :: (Logic a, Container cont (L a)) =>  cont -> cont
strip_any_literals cont = case is_empty(cont) of 
                              True  -> empty_container
                              False -> case get_from_container cont of
                                   (M mod y) -> add_to_container (head y) (strip_any_literals (remove_from_container cont))
                                   _         -> strip_any_literals (remove_from_container cont)

-- Strip any modal operator from all negative occurences. Remove all other formulae
strip_any_nliterals :: (Container cont (L a)) =>  cont -> cont
strip_any_nliterals cont = case is_empty(cont) of 
                 True -> empty_container
                 False -> case get_from_container cont of
                    (Neg (M mod y)) -> add_to_container (head y) (strip_any_nliterals (remove_from_container cont))
                    _               -> strip_any_nliterals (remove_from_container cont)

-- Strip specified modal operator from all positive occurences. Remove all other formulae
strip_literals :: (Logic a, Container cont (L a)) => a -> cont -> cont
strip_literals mod cont = case is_empty(cont) of 
                 True -> empty_container
                 False -> case get_from_container cont of
                    (M mod y) -> add_to_container (head y) (strip_literals mod (remove_from_container cont))
                    _         -> strip_literals mod (remove_from_container cont)

-- Strip specified modal operator from all negative occurences. Remove all other formulae
strip_nliterals :: (Logic a, Container cont (L a)) => a -> cont -> cont
strip_nliterals mod cont = case is_empty(cont) of 
                 True -> empty_container
                 False -> case get_from_container cont of
                    (Neg(M mod y)) -> add_to_container (head y) (strip_nliterals mod (remove_from_container cont))
                    _              -> strip_nliterals mod (remove_from_container cont)

-- Strip specified modal operator from all negative occurences. Remove all other formulae
strip_nliterals_bin :: (Logic a, Container cont (L a)) => a -> cont -> cont
strip_nliterals_bin mod cont = case is_empty(cont) of 
                     True -> empty_container
                     False -> case get_from_container cont of
                        (Neg(M mod y)) -> add_to_container (head (tail y))
                                                           (strip_nliterals_bin mod (remove_from_container cont))
                        _              -> strip_nliterals_bin mod (remove_from_container cont)

-- Strip negation from each negated formula in container. Remove all other formulae
strip_neg :: (Logic a, Container cont (L a)) => cont -> cont
strip_neg cont = case is_empty(cont) of 
                  True -> empty_container
                  False -> case get_from_container cont of
                     (Neg(phi)) -> add_to_container (phi) (strip_neg (remove_from_container cont))
                     _          -> strip_neg (remove_from_container cont)

-- Negate each formula in a container
negate_container :: (Logic a, Container cont (L a)) => cont -> cont
negate_container cont = container_map (\phi -> Neg phi) cont

-- Create the conjuction of all elements of a container.
-- Needed for matching of G, P
conjunct_container :: (Logic a, Container cont (L a)) => cont -> L a
conjunct_container cont = case is_empty(cont) of 
                        True  -> F;
                        False -> case is_empty(remove_from_container cont) of
                                 True  -> get_from_container cont
                                 False -> And (get_from_container cont) (conjunct_container (remove_from_container cont))

-- Remove all formulas from a container that are not positive modal literals
keep_poslits :: (Logic a, Container cont (L a)) => cont -> cont
keep_poslits seq = container_filter (\phi -> case phi of (M _ psi)->True;_->False) seq

-- Remove all formulas from a container that are not negative modal literals
keep_neglits :: (Logic a, Container cont (L a)) => cont -> cont
keep_neglits seq = container_filter (\phi -> case phi of (Neg(M _ psi))->True;_->False) seq

--------------------------------------------------------------------------------
-- Some functions for easy distinguishing of formulae, sequents, premises
-- and lists of premises
--------------------------------------------------------------------------------

-- Avoids []->[[]], otherwise F matches F
listify :: [a] -> [[a]]
listify [] = []; listify x = [x]

-- Create a list of premises containing just one premise
only_this_premise :: (Logic a) => Premise a -> [Premise a]
only_this_premise = listify

-- Create a premise containing just one sequent
premisify :: (Logic a) => Sequent a -> Premise a
premisify =  listify

-- Create a sequent containing just one formula
sequentify :: (Logic a) => L a -> Sequent a
sequentify phi =  add_to_container phi empty_container

--------------------------------------------------------------------------------
-- instances of the logics
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- instance of logic K
--------------------------------------------------------------------------------
data K = K deriving (Eq,Show)

-- For each positive modal literal, there is a premise containing only one
-- sequent. This sequent contains the stripped positive literal and all
-- negated stripped negative literals.
-- e.g. seq       = [ (M K p), !(M K q), (M K !p), !(M K !r)]
--      match seq = [ [[ p, !q, r]], [[ !p, !q, r]] ]

instance Logic K where
	match seq = let neglits = negate_container $ strip_nliterals K seq
                        poslits = strip_literals K seq
                    in map premisify (container_map (container_add neglits) poslits)

--------------------------------------------------------------------------------
-- instance of logic KD
--------------------------------------------------------------------------------
data KD = KD deriving (Eq,Show)

-- For each positive modal literal, there is a premise containing only one
-- sequent. This sequent contains the stripped positive literal and all
-- negated stripped negative literals. Also there is an additional premise,
-- containing the sequent of all negated stripped negative literals.
-- e.g. seq       = [ (M KD p), !(M KD q), (M KD !p), !(M KD !r)]
--      match seq = [ [[ p, !q, r]], [[ !p, !q, r]], [[!q, r]] ]

instance Logic KD where
	match seq = let neglits = negate_container $ strip_nliterals KD seq
                        poslits = strip_literals KD seq
                     in map premisify (container_map (container_add neglits) poslits)
                        ++ (only_this_premise $ premisify neglits)

--------------------------------------------------------------------------------
-- instance of Hennessy-Milner logic
--------------------------------------------------------------------------------
data HM = HM Char deriving (Eq,Show)

-- For each positive modal literal, there is a premise containing only one
-- sequent. This sequent contains the stripped positive literal and all
-- negated stripped negative literals with the same index.
-- e.g. seq       = [ (M (HM a) p), !(M (HM b) q), (M (HM b) !p), !(M (HM a) !r)]
--      match seq = [ [[ p, r]], [[ !p, r]] ]

instance Logic HM where
    match seq = let neglits ind = negate_container $ strip_nliterals (HM ind) seq
                in [ premisify (add_to_container (head phi) (neglits ind)) | (M (HM ind) phi) <- seq]

--------------------------------------------------------------------------------
-- instance of Monotonic logic
--------------------------------------------------------------------------------
data Mon = Mon deriving (Eq,Show)

-- For any combination of a positive and a negative literal, there is a premise
-- containing only one sequent. This sequent contains only one formula over the
-- stripped positive literal and the negated stripped negative literal.
-- e.g. seq       = [ (M Mon p), !(M Mon q), (M Mon !p), !(M Mon !r)]
--      match seq = [ [[ p, !q]], [[p, r]], [[ !p, !q]], [[ !p, r]] ]

instance Logic Mon where
	match seq = let neglits = negate_container $ strip_nliterals Mon seq
                        poslits = strip_literals Mon seq
                    in [ premisify (sequentify (Neg (And (Neg phi) (Neg psi)))) | phi <- neglits, psi <- poslits]

--------------------------------------------------------------------------------
-- instance of Coalition logic and needed functions
--------------------------------------------------------------------------------
data C = C [Int] deriving (Eq,Show)

-- For each positive modal literal, there are possibly serveral premises,
-- containing only one sequent each. This sequent contains the stripped positive
-- literal and additional stripped literals which are computed by
-- 'c_build_matches'. Also there is one additional premise, containing the sequent
-- of all negated stripped negative literals.
-- e.g. seq       = [ (M (C [0,3]) p), !(M (C [0]) q), (M (C [0,2,3]) !p), !(M (C [1]) !r)]
--      match seq = [ [[ p, !p, !q ]], [[ p, !p, !q]], [[!q, r]] ]
instance Logic C where
	match seq = let neglits =  negate_container $ strip_any_nliterals seq
                        poslits =  strip_any_literals seq
                    in map premisify (container_map (container_cons poslits)
                                                    (c_build_matches (keep_poslits seq) (keep_neglits seq)))
                       ++ only_this_premise(premisify neglits)

-- Form negative literal parts of matching premise for positive literals
c_build_matches :: [L C] -> [L C] -> [[L C]]
c_build_matches [] _ = []
c_build_matches ( (M (C pset) pphi):pls) nls =
	let relevant_neglits = filter (\(Neg(M(C s)_)) -> ((s `intersect` pset)==s)) nls
	    relevant_ncoalitions = nub $ map (\(Neg(M(C s)_)) -> s) relevant_neglits
	    maximal_pw_dis_lists = rm_sublists $ sortBy compare_length 
                                                        (filter (pairwise_disjunct) (pwrset relevant_ncoalitions))
 	    negmats = map negate_container (map (strip_any_nliterals)
                                                (concatMap (build_lit_lists relevant_neglits) maximal_pw_dis_lists)) 
	in  (map ([head pphi]++) negmats) ++ (c_build_matches pls nls)
  
-- Given a list of negative literals and a list of pairwise disjunctive lists, form pairwise
-- disjunctive lists of the according literals
build_lit_lists :: [L C] -> [[Int]] -> [[L C]]
build_lit_lists _ [] = [[]]
build_lit_lists lits (set:sets) = let relevant_neglits = filter (\(Neg(M(C t)_)) -> set==t) lits
	                          in if null(relevant_neglits) then [] else
		                            (map ([head relevant_neglits]++) (build_lit_lists lits sets)) 
                                                 ++ (build_lit_lists (lits\\[head relevant_neglits]) (set:sets))

-- Does the list contain only pairwise disjunct lists?
pairwise_disjunct :: (Eq a) => [[a]] -> Bool
pairwise_disjunct [] = True
pairwise_disjunct (x:xs) = if (all (\y -> null(x `intersect` y)) xs) then (pairwise_disjunct xs) else False
	
-- Remove sublists (i.e. keep only maximal lists). Requires input to be sorted
rm_sublists :: (Eq a) => [[a]] -> [[a]]
rm_sublists [] = []
rm_sublists (x:xs) | (any (\y -> (x `intersect` y == x)) xs) = rm_sublists(xs)
                   | otherwise = x:rm_sublists(xs) 

-- Compare lists by size.
compare_length :: [a] -> [a] -> Ordering
compare_length s t = if(length(s) < length(t)) then LT else GT

--------------------------------------------------------------------------------
-- instance of Graded Modal Logic and needed functions
--------------------------------------------------------------------------------
data G = G Int deriving (Eq,Show)	

instance Logic G where
    match seq = let poslits = keep_poslits seq
                    neglits = keep_neglits seq
                    -- take all combinations of positive and negative modal literals
                    all_combinations = [ (pos,neg) |
                                pos <- (pwrset poslits), neg <- (pwrset neglits)] \\ [([],[]) ]
                    multiplicities xs = map (\(M(G k)_) -> k) xs
                    side_condition_tuples (p,n) = 
                       let switch l = map (\(x,y)->(y,map negate x)) l
                       in switch $ ineqSolver (Coeffs (map (1+) (multiplicities (strip_neg n))) (multiplicities p))
                                              (gml_bound ((multiplicities p),(multiplicities (strip_neg n))))
                    gml_match (ps,ns) = map (gml_build_matches (ps,ns))
                                            (gml_filter_tuples (side_condition_tuples (ps,ns)) [] )
                in (nub $ map gml_match all_combinations) \\ [[]]

gml_build_matches :: ([L G],[L G]) -> ([Int],[Int]) -> [L G]
gml_build_matches (poslits,neglits) (prs,nrs) =
 	      let (pos_inds,neg_inds) = (to_inds prs,to_inds nrs)
		  all_inds = [(pos,neg) | pos <- (pwrset pos_inds), neg <- (pwrset neg_inds)]
	 	  (sposlits,sneglits) = (strip_any_literals poslits,strip_any_nliterals neglits)
		  relevant_inds = filter (\(pos,neg) -> (sum $ img pos prs) < (sum $ img neg nrs)) all_inds
		  getJ (ps,ns) = (img ps sposlits) ++ (img ns sneglits)
		  getnJ (ps,ns) = (img (pos_inds \\ ps) sposlits) ++ (img (neg_inds \\ ns) sneglits)
              in nub $ map (\rs -> Neg (conjunct_container (nub ((map nneg (getnJ rs)) ++ (getJ rs)))) ) relevant_inds

-- GML bound on integer magnitude
gml_bound :: ([Int],[Int]) -> Int
gml_bound (kps,kns) = 
	let	n = (length kps) + (length kns)
		logint k x = ceiling $ logBase 2 (k + x)
		logsum ls k = sum $ map (\x -> logint k (fromIntegral(x))) ls	
	in	12*n*(1+n) + 6*n*((logsum kps 1) + (logsum kns 2))

gml_filter_tuples :: [([Int], [Int])] -> [([Int], [Int])] -> [([Int], [Int])]
gml_filter_tuples [] bs = bs
gml_filter_tuples (a:as) bs
      | any (\x -> gml_geq x a) bs = gml_filter_tuples as bs
      | otherwise = a:(filter (\x -> not (gml_leq x a)) bs)

gml_leq ::  ([Int],[Int]) ->  ([Int],[Int]) -> Bool
gml_leq (p1, n1) (p2, n2) =  (and (( map (\(x, y) -> x <= y) (( zip p1 p2) ++ (zip  n1 n2)))))

gml_geq ::  ([Int],[Int]) ->  ([Int],[Int]) -> Bool
gml_geq (p1, n1) (p2, n2) =  (and (( map (\(x, y) -> x >= y) (( zip p1 p2) ++ (zip  n1 n2)))))

--------------------------------------------------------------------------------
-- instance of Probabilistic Modal Logic and needed functions
--------------------------------------------------------------------------------
data P = P Rational deriving (Eq,Show)

instance Logic P where
	match seq = let poslits = keep_poslits seq
                        neglits = keep_neglits seq
                        -- take all combinations of positive and negative modal operators
                        all_combinations = [ (pos, neg) |
                                    pos <- map nub (pwrset poslits), neg <- map nub (pwrset neglits)] \\ [([],[])]
                        probabilities xs = map (\(M(P k)_) -> k) xs
		        bound (p,n) = pml_bound ((probabilities p),(probabilities (strip_neg n)))
	                tuples (p,n) = nub [(pts,nts,k)| pts <- (tuprange (bound (p,n)) (length p)), 
		        			     nts <- (tuprange (bound (p,n)) (length n)),
		 	         	             k <- [-(bound (p,n))..(bound (p,n))]]
		        side_condition_tuples (p,n) = filter (pml_side_condition (p,n)) (tuples (p,n))
		        pml_match (p,n) = trace ("\n  filtered tuples:" ++ show((pml_filter_tuples (side_condition_tuples (p,n)) []))) $
                                              map (pml_build_matches (p,n))
                                              (pml_filter_tuples (side_condition_tuples (p,n)) [])
                in trace ("\n  allc:" ++ show(map (pair (map pretty) (map pretty)) all_combinations)) $
                   (nub $ (map pml_match all_combinations)) \\ [[]]

pml_build_matches :: ([L P],[L P]) -> ([Int],[Int],Int) -> [L P]
pml_build_matches (poslits,neglits) (prs,nrs,k) =
	let	(pos_inds,neg_inds) = (to_inds prs,to_inds nrs)
		all_inds = [(pos,neg) | pos <- (pwrset pos_inds), neg <- (pwrset neg_inds)]
		(sposlits,sneglits) = (strip_any_literals poslits,strip_any_nliterals neglits)
		relevant_inds = filter (\(pos,neg) -> (sum $ img pos prs) - (sum $ img neg nrs) < k) all_inds
		getJ (ps,ns) = (img ps sposlits) ++ (img ns sneglits)
		getnJ (ps,ns) = (img (pos_inds \\ ps) sposlits) ++ (img (neg_inds \\ ns) sneglits)
        in nub $ (map (\rs -> Neg (conjunct_container ((map nneg (getnJ rs)) ++ (getJ rs))) ) relevant_inds)

pml_side_condition :: ([L P],[L P]) -> ([Int],[Int],Int) -> Bool
pml_side_condition (pls,nls) (pints,nints,k) =
	let	(rpints,rnints) = (map fromIntegral pints,map fromIntegral nints)
		psum = sum $ zipbin (*) rpints (map (\(M(P x)_)->fromRational(x)) pls)
		nsum = sum $ zipbin (*) rnints (map (\(Neg(M(P x)_))-> fromRational(-x)) nls)
	in	if null(pints) 	then (psum + nsum < fromIntegral(k))
						else (psum + nsum <= fromIntegral(k))

pml_bound :: ([Rational],[Rational]) -> Int
pml_bound (rps,rns) = 
	let	n = (length rps) + (length rns)
		toints rs = concatMap (\r -> [numerator r,denominator r]) rs
		allints = (toints rps) ++ (toints rns)
		logint x = ceiling(logBase 2 (1 + x))
		logsum = sum $ map (\y -> logint (fromIntegral(y))) allints
	in	20*n*n*(1+n) + 10*n*n*logsum

-- find maximal elts of those tuples satisfying the side condition
pml_filter_tuples :: [([Int], [Int], Int)] -> [([Int], [Int], Int)] -> [([Int], [Int], Int)]
pml_filter_tuples [] bs = bs
pml_filter_tuples (a:as) bs
		 | any (\x -> pml_geq x a) bs = pml_filter_tuples as bs
		 | otherwise = a:(filter (\x -> not (pml_leq x a)) bs)

pml_leq ::  ([Int],[Int], Int) ->  ([Int],[Int], Int) -> Bool
pml_leq (p1, n1, k1) (p2, n2, k2) = (k1 == k2) && (and (( map (\(x, y) -> x <= y) (( zip p1 p2) ++ (zip  n1 n2)))))

pml_geq ::  ([Int],[Int], Int) ->  ([Int],[Int], Int) -> Bool
pml_geq (p1, n1, k1) (p2, n2, k2) = (k1 == k2) && (and (( map (\(x, y) -> x >= y) (( zip p1 p2) ++ (zip  n1 n2)))))

-- Construct all integer n-tuples with elements from 1,..,r
tuprange :: Int -> Int -> [[Int]]
tuprange _ 0 = [[]]
tuprange r n = 
	let rec xs ys = map (\z -> z:ys) xs
	in	concatMap (rec [1..r]) (tuprange r (n-1))

-- zip two lists together using a binary operator
zipbin :: (a -> a -> a) -> [a] -> [a] -> [a]
zipbin _ [] _ = [];	zipbin _ _ [] = [];
zipbin f (x:xs) (y:ys) = (f x y):(zipbin f xs ys)

--------------------------------------------------------------------------------
-- instance of Conditional Modal Logic and needed functions
--------------------------------------------------------------------------------
data Con = Con deriving (Eq,Show)	

instance Logic Con where

-- For any set of logically equivalent premises A1,...,An, there are two premises:
-- The first premise contains the (negated) stripped conclusions of (negative)
-- literals with a premise from A1,...,An.
-- The second premise contains just the statement that all A1,...,An are
-- logically equivalent.
    match seq = let neglits premises = negate_container $ [ phi | (Neg(M Con (psi:phi:_))) <- seq, psi `elem` premises]
                    poslits premises = [ phi | (M Con (psi:phi:_)) <- seq, psi `elem` premises]
                in [ trace ("\n  prems:" ++ show(map pretty prems)) $
                     premisify(container_cons (neglits prems) (poslits prems)) ++
                     premisify(are_equiv prems) | prems <- (equivalent_premises (con_premises seq))] \\ [[]]

-- create sequent stating that all elements of the input list are equivalent to the
-- input formula.
are_equiv :: (Logic a) => [L a] -> Sequent a
are_equiv [] = empty_container
are_equiv (psi:[]) = empty_container
are_equiv (psi:phi:xs) =  (And (Neg (And (Neg psi) phi)) (Neg (And (Neg phi) psi))) : (are_equiv (psi:xs))

-- return true if both input formulae are logically equivalent
equivalent :: (Logic a) => L a -> L a -> Bool
equivalent phi psi = trace ("\n  just trying...") $ 
                     sequent_provable (And (Neg (And (Neg psi) phi)) (Neg (And (Neg phi) psi)))

-- return list of all formulae from input list which are equivalent to input formula
equivalence_class :: (Logic a) => L a -> [L a] -> [L a]
equivalence_class phi [] = []
equivalence_class phi (x:xs) = case (equivalent phi x) of
                                  True -> x:(equivalence_class phi xs)
                                  False -> (equivalence_class phi xs)

-- return list of equivalence-classes of a list of formulae
equivalent_premises :: (Logic a) => [L a] -> [[L a]]
equivalent_premises [] = [[]]
equivalent_premises (x:xs) = let eq_class = nub (x:(equivalence_class x xs))
                             in eq_class : equivalent_premises ((x:xs) \\ eq_class)

-- return the premises of each positive or negative literal in the input sequent
con_premises :: (Logic Con) => Sequent Con -> [L Con]
con_premises seq = [psi | (M Con (psi:phi:_)) <- seq] ++ [psi | (Neg(M Con (psi:phi:_))) <- seq]

--------------------------------------------------------------------------------
-- auxiliary functions for the matching functions
--------------------------------------------------------------------------------

-- Get powerlist of a list
-- Needed in matching of C, G, P
pwrset :: [a] -> [[a]]
pwrset [] = [[]]
pwrset (x:xs) = (map ([x]++) (pwrset xs)) ++ (pwrset xs)

-- Get the elements of a list that are indexed by the first parameter list
-- Needed for 'normal-forms' of G, P
img :: [Int] -> [a] -> [a]
img inds xs = map (xs!!) inds 

-- Get list [0..(length xs)-1]
-- Needed for 'normal-forms' of G, P
to_inds :: [a] -> [Int]
to_inds [] = []
to_inds xs = [0..(length xs)-1]

-- Normalised negation.
-- Needed for matching of G, P
nneg :: L a -> L a
nneg F = T
nneg T = F
nneg (Neg phi) = phi
nneg phi = (Neg phi)
