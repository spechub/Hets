{- | Module     : $Header$
 -  Description : Implementation of logic formula parser
 -  Copyright   : (c) Georgel Calin & Lutz Schroeder, DFKI Lab Bremen,
 -                Rob Myers & Dirk Pattinson, Department of Computing, ICL 
 -  License     : Similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
 -  Maintainer  : g.calin@jacobs-university.de
 -  Stability   : provisional
 -  Portability : portable
 -
 - Provides the implementation of the generic algorithm for checking 
 - satisfiability/provability of several types of modal logics.
 -}
module GMP.Generic where
import List
import Ratio
import Maybe
import GMP.IneqSolver
import Debug.Trace
-- import Hugs.Observe
-- trace :: String -> a -> a; trace _ a = a;

-- Modal logic type with Clause type and Logic class
data L a
	=  F | T | Atom Int 
		| Neg (L a) | And (L a) (L a) | Or (L a) (L a)
		| M a (L a)
	deriving (Eq,Show)

-- convention: Clause(pos literals,neg literals)
newtype Clause a = Clause ([L a],[L a]) deriving (Eq,Show)

-- Logic class: consists of a Modal logic type with a rule for matching clauses
class (Eq a,Show a) => Logic a where 
	match :: Clause a -> [[L a]]


-- instance of logic K
data K = K deriving (Eq,Show)

instance Logic K where
	match (Clause (pl,nl)) =
		let (nls,pls) = (map neg (stripany nl), stripany pl)
		in map disjlst (map (\x -> x:nls) pls)
			

-- instance of logic KD
data KD = KD deriving (Eq,Show)

instance Logic KD where
	match (Clause (pl,nl)) = 
		let	(nls,pls) = (map neg (strip KD nl), strip KD pl)
			xnls = listify nls
		in map disjlst ((map (\x -> x:nls) pls) ++ xnls)
		
-- instance of Hennessy-Milner logic
data HM = HM Char deriving (Eq,Show)
instance Logic HM where
	match (Clause (pl,nl)) =
		-- is it agent a?
		let	isag a (M (HM ind) _) = (ind == a);
			isag _ _ = False;
		-- find the agent
			ag (M (HM ind) _) = Just ind;
			ag _ = Nothing;
		-- the set of agents we have
			ags = nub $ catMaybes (map ag (pl ++ nl));
			aglits = map (\x -> (filter (isag x) pl, filter (isag x) nl)) ags;
		-- this is a list of pairs (pl, nl) for each agent
			strlits  = map (\(x, y) -> ((stripany x), map neg (stripany y))) aglits;
		-- the same with boxes stripped
			comb (pls, nls) = map disjlst (map (\x -> x:nls) pls);
		-- turn a combination pls/nls into a list of formulas
			fllist = map comb strlits;
		-- a list of lists consisting of formulas
	  in	concat fllist
		
-- instance of Monotonic logic Mon
data Mon = Mon deriving (Eq,Show)

instance Logic Mon where
	match (Clause (pl,nl)) =
		let (nls,pls) = (map neg (strip Mon nl), strip Mon pl)
		in [[Or phi psi] | phi <- nls,  psi <- pls]
		

-- instance of Coalition logic
data C = C [Int] deriving (Eq,Show)
agents :: Int; agents = 10

instance Logic C where
	match (Clause (pls,nls)) =
		let	pNs = strip (C [1..agents]) pls
			(bnls,bpls) = (onlyboxes nls, onlyboxes pls)
			allneg = map (neg) (stripany nls)
			xallneg = listify allneg
		in map disjlst ((map (pNs++) (cmatch bpls bnls)) ++ xallneg) 

-- form 'pw disj subsets of +ve lit' parts of matching clause
cmatch :: [L C] -> [L C] -> [[L C]]
cmatch [] _ = []
cmatch ((M(C pset) pphi):pls) nls =
	let	subnls = filter (\(M(C s)_) -> ((s `intersect` pset)==s)) nls
		sublsts = nub $ map (\(M(C s)_) -> s) subnls
		maxpwdjs = rmsub $ sortBy cmpsize (filter (pwdisj) (pwrset sublsts))
 		negmats = map (neglst) (map (stripany) (concatMap (ch subnls) maxpwdjs)) 
	in	(map ([pphi]++) negmats) ++ (cmatch pls nls)
  
-- given lits and pairwise disj lists, form pairwise disj lit lists
ch :: [L C] -> [[Int]] -> [[L C]]
ch _ [] = [[]]
ch lits allsets@(set:sets) =
	let ls = filter (\(M(C t)_) -> set==t) lits
	in	if null(ls) then [] else
		(map ([head ls]++) (ch lits sets)) ++ (ch (lits\\[head ls]) allsets)
	
	
-- instance of Graded Modal Logic
data G = G Int deriving (Eq,Show)	

instance Logic G where
    match (Clause(pls,nls)) =
        let (bpls,bnls) = (onlyboxes pls, onlyboxes nls)
            allcls = [Clause(ps,ns) |
                        ps <- (pwrset bpls), ns <- (pwrset bnls)] \\ [Clause([],[])]
            xints xs = map (\(M(G k)_) -> k) xs
            bnd (Clause(ps,ns)) = gmlbnd ((xints ps),(xints ns))
            {-
            tups cl@(Clause(ps,ns)) = 
                [(pts,nts)|	pts <- (tuprange (bnd cl) (length ps)), 
                            nts <- (tuprange (bnd cl) (length ns))]
            sctups cl = let res = filter (gmlsc cl) (tups cl)
                            bound = bnd cl
                        in trace("clause: "++show cl++", sctups: "++ {-show res-}++", bound: " ++ show bound
                                           ++", n: "++show n++", p: "++ show pp) res
            -}
            sctups cl@(Clause(p,n)) = 
                let switch l = map (\(x,y)->(y,map negate x)) l
                in switch $ ineqSolver (Coeffs (map (1+) (xints n)) (xints p)) (bnd cl)
            
            -- find maximal elts of those tupes satisfying the side condition
            leq ::  ([Int],[Int]) ->  ([Int],[Int]) -> Bool
            leq (p1, n1) (p2, n2) =  (and (( map (\(x, y) -> x <= y) (( zip p1 p2) ++ (zip  n1 n2)))))
            geq ::  ([Int],[Int]) ->  ([Int],[Int]) -> Bool
            geq (p1, n1) (p2, n2) =  (and (( map (\(x, y) -> x >= y) (( zip p1 p2) ++ (zip  n1 n2)))))
            ftups :: [([Int], [Int])] -> [([Int], [Int])] -> [([Int], [Int])]
            ftups [] bs = bs
            ftups (a:as) bs
                | any (\x -> geq x a) bs = ftups as bs
                | otherwise = a:(filter (\x -> not (leq x a)) bs)
            -- clmatch cl = map (gmlcnf cl) (sctups cl) 
            clmatch cl = map (gmlcnf cl) (ftups (sctups cl) [] )
         in nub $ concatMap clmatch allcls
		-- in trace("For bpls="++show bpls++" and bnls="++show bnls++" allcls is: "++show allcls) nub $ concatMap clmatch allcls

-- GML CNF: given clause & tuple output cnf
-- e.g. clause (pos as,neg as) -> (pos rs,neg rs), 
-- then find all combinations whose sum is less than 0
gmlcnf :: Clause G -> ([Int],[Int]) -> [L G]
gmlcnf (Clause(pls,nls)) (prs,nrs) =
	let	(pinds,ninds) = (toinds prs,toinds nrs)
		(spls,snls) = (stripany pls,stripany nls)
		allinds = [(ps,ns) | ps <- (pwrset pinds), ns <- (pwrset ninds)]
		cnfinds = filter (\(ps,ns) -> (sum$img ps prs)<(sum$img ns nrs)) allinds
		getJ (ps,ns) = (img ps spls) ++ (img ns snls)
		getnJ (ps,ns) = (img (pinds \\ ps) spls) ++ (img (ninds \\ ns) snls)
	-- in	map (\rs -> ndisj(getJ rs) \/ disj(getnJ rs)) cnfinds
  in nub $ map (\rs -> c2f (Clause ((getnJ rs),(getJ rs))) ) cnfinds



-- GML side condition
gmlsc :: Clause G -> ([Int],[Int]) -> Bool
gmlsc (Clause(pls,nls)) (pints,nints) =
	let	psum = sum $ zipbin (*) pints (map (\(M(G k)_)->fromIntegral(k)) pls)
		nsum = sum $ zipbin (*) nints (map (\(M(G k)_)->1+fromIntegral(k)) nls)
	in	nsum >= 1 + psum
	
-- GML bound on integer magnitude
gmlbnd :: ([Int],[Int]) -> Int
-- gmlbnd _ = 1
gmlbnd (kps,kns) = 
	let	n = (length kps) + (length kns)
		logint k x = ceiling $ logBase 2 (k + x)
		logsum ls k = sum $ map (\x -> logint k (fromIntegral(x))) ls	
	in	12*n*(1+n) + 6*n*((logsum kps 1) + (logsum kns 2))
		

-- instance of Probabilistic Modal Logic
data P = P Rational deriving (Eq,Show)

instance Logic P where
	match (Clause(pls,nls)) =
		let	(bpls,bnls) = (onlyboxes pls, onlyboxes nls)
			allcls = [Clause(ps,ns) | 
				ps <- (pwrset bpls), ns <- (pwrset bnls)] \\ [Clause([],[])]
			xrats xs = map (\(M(P k)_) -> k) xs
			bnd (Clause(ps,ns)) = pmlbnd ((xrats ps),(xrats ns))
			tups cl@(Clause(ps,ns)) = 
				[(pts,nts,k)|	pts <- (tuprange (bnd cl) (length ps)), 
								nts <- (tuprange (bnd cl) (length ns)),
								k <- [-(bnd cl)..(bnd cl)]]
			sctups cl = filter (pmlsc cl) (tups cl)
			-- find maximal elts of those tupes satisfying the side condition
			leq ::  ([Int],[Int], Int) ->  ([Int],[Int], Int) -> Bool
			leq (p1, n1, k1) (p2, n2, k2) = (k1 == k2) && (and (( map (\(x, y) -> x <= y) (( zip p1 p2) ++ (zip  n1 n2)))))
			geq ::  ([Int],[Int], Int) ->  ([Int],[Int], Int) -> Bool
			geq (p1, n1, k1) (p2, n2, k2) = (k1 == k2) && (and (( map (\(x, y) -> x >= y) (( zip p1 p2) ++ (zip  n1 n2)))))
			ftups :: [([Int], [Int], Int)] -> [([Int], [Int], Int)] -> [([Int], [Int], Int)]
			ftups [] bs = bs
			ftups (a:as) bs
				| any (\x -> geq x a) bs = ftups as bs
				| otherwise = a:(filter (\x -> not (leq x a)) bs)
			-- clmatch cl = map (pmlcnf cl) (sctups cl)
			clmatch cl = map (pmlcnf cl) (ftups (sctups cl) [] )
		in	nub $ concatMap clmatch allcls

pmlcnf :: Clause P -> ([Int],[Int],Int) -> [L P]
pmlcnf (Clause(pls,nls)) (prs,nrs,k) =
	let	(pinds,ninds) = (toinds prs,toinds nrs)
		(spls,snls) = (stripany pls,stripany nls)
		allinds = [(ps,ns) | ps <- (pwrset pinds), ns <- (pwrset ninds)]
		cnfinds = filter (\(ps,ns) -> (sum$img ps prs) - (sum$img ns nrs) < k) allinds
		getJ (ps,ns) = (img ps spls) ++ (img ns snls)
		getnJ (ps,ns) = (img (pinds \\ ps) spls) ++ (img (ninds \\ ns) snls)
	in	map (\rs -> ndisj(getJ rs) \/ disj(getnJ rs)) cnfinds

pmlsc :: Clause P -> ([Int],[Int],Int) -> Bool
pmlsc (Clause(pls,nls)) (pints,nints,k) =
	let	(rpints,rnints) = (map fromIntegral pints,map fromIntegral nints)
		psum = sum $ zipbin (*) rpints (map (\(M(P x)_)->fromRational(x)) pls)
		nsum = sum $ zipbin (*) rnints (map (\(M(P x)_)-> fromRational(-x)) nls)
	in	if null(pints) 	then (psum + nsum < fromIntegral(k))
						else (psum + nsum <= fromIntegral(k))

pmlbnd :: ([Rational],[Rational]) -> Int
-- pmlbnd _ = 5
pmlbnd (rps,rns) = 
	let	n = (length rps) + (length rns)
		toints rs = concatMap (\r -> [numerator r,denominator r]) rs
		allints = (toints rps) ++ (toints rns)
		logint x = ceiling(logBase 2 (1 + x))
		logsum = sum $ map (\y -> logint (fromIntegral(y))) allints
	in	20*n*n*(1+n) + 10*n*n*logsum

{-
---------
main code
---------
-}
{- Code not needed in CoLoSS+Parser

-- syntactic sugar
(-->) :: L a -> L a -> L a
phi --> psi = Or (Neg phi) psi

(/\) :: L a -> L a -> L a
phi /\ psi = And phi psi
-}

(\/) :: L a -> L a -> L a
phi \/ psi = Or phi psi

{-
(<->) :: L a -> L a -> L a
phi <-> psi = (phi --> psi) /\ (psi --> phi)

p :: Int -> L a; p x = Atom x
-}

-- negation
neg :: L a -> L a; neg F = T; neg T = F; neg a = Neg a
-- normalised negation
nneg :: L a -> L a; nneg F = T; nneg T = F; nneg (Neg phi) = phi; nneg phi = (Neg phi)


{- Code not needed in CoLoSS + Parser

infixr 8 /\
infixr 6 \/
infixr 4 -->
infixr 2 <->

-- pretty print logic
pretty :: (Logic a) => L a -> String
pretty F = "ff"; pretty T = "tt";
pretty (Atom k) = "p" ++ (show k);
pretty (Or (Neg x) y) = "(" ++ (pretty x) ++ " --> " ++ (pretty y) ++ ")"
pretty (Neg x) = "(not (" ++  (pretty x) ++ "))"
pretty (Or x y) = "(" ++ (pretty x) ++ " or " ++ (pretty y) ++ ")"
pretty (And x y) = "(" ++ (pretty x) ++ " and " ++ (pretty y) ++ ")"
pretty (M a x) = "[" ++ (show a) ++ "](" ++ (pretty x) ++ ")"

-- pretty print clause
prettycl :: (Logic a) => Clause a -> String
prettycl (Clause(pls,nls)) = pretty ((disj pls) \/ (ndisj nls))

-- pretty print matchings
mpretty :: (Logic a) => [[L a]] -> String
mpretty [] = "\n\t...finished"
mpretty (m:ms) = "\n\t" ++ (show (map pretty m)) ++ mpretty(ms)

-}

-- avoids []->[[]], otherwise F matches F
listify :: [a] -> [[a]]
listify [] = []; listify x = [x]


-- generic stripper
-- strip particular boxes & remove other formulae
strip :: (Logic a) => a -> [L a] -> [L a]
strip a (M b y:xs) | (a == b) = y:(strip a xs)
strip a (_:xs) = strip a xs
strip _ [] = []

-- strip any boxes
stripany :: (Logic a) => [L a] -> [L a]
stripany xs = foldr (\x y -> case x of (M _ phi)->phi:y;_{-otherwise-}->y) [] xs

-- drop non-boxed formulae
onlyboxes :: (Logic a) => [L a] -> [L a]
onlyboxes xs = filter (\x -> case x of (M _ _)->True; _{-otherwise-} -> False) xs

neglst :: [L a] -> [L a]
neglst xs = map neg xs 

-- disjunctions & conjunctions
disj :: [L a] -> L a
disj [] = F; disj [a] = a; disj (a:as) = Or a (disj as)

conj :: [L a] -> L a
conj [] = F; conj [a] = a; conj (a:as) = And a (conj as)

ndisj :: [L a] -> L a; ndisj xs = disj (map nneg xs)

disjlst :: [L a] -> [L a]; disjlst x = [disj x]

-- all possible clauses
clauses :: [L a] -> [Clause a]
clauses [] = [Clause ([],[])]
clauses (a:as) = 
	let	padd c (Clause (p, n)) = Clause (c:p, n)
		nadd c (Clause (p, n)) = Clause (p, c:n)
	in	(map (padd a) (clauses as)) ++ (map (nadd a) (clauses as))
	
-- modal atoms
ma :: (Logic a) => L a -> [L a]
ma F = []
ma T = []
ma (And phi psi) = (ma phi) `union` (ma psi)
ma (Or phi psi) = (ma phi) `union` (ma psi)
ma (Neg phi) = ma phi
ma (M a phi) = [M a phi]
ma (Atom x) = [Atom x]
{- code not needed in CoLoSS+Parser

-- produce (iterated) boxes
box :: a -> L a -> L a; box a x = (M a) x 

ibox :: Int -> a -> L a -> L a
ibox 0 _ f = f
ibox n a f = (M a) (ibox (n-1) a f)

iter :: (L a -> L a -> L a) -> Int -> a -> L a -> L a
iter _ 0 _ f = f 
iter c n a f = (ibox n a f) `c`  (iter c (n-1) a f)

-}

-- zip two lists together using a binary operator
zipbin :: (a -> a -> a) -> [a] -> [a] -> [a]
zipbin _ [] _ = [];	zipbin _ _ [] = [];
zipbin f (x:xs) (y:ys) = (f x y):(zipbin f xs ys)

img :: [Int] -> [a] -> [a]; img inds xs = map (xs!!) inds 
toinds :: [a] -> [Int]; toinds [] = []; toinds xs = [0..(length xs)-1]

-- construct all integer n-tuples with elements from 1,..,r
tuprange :: Int -> Int -> [[Int]]
tuprange _ 0 = [[]]
tuprange r n = 
	let rec xs ys = map (\z -> z:ys) xs
	in	concatMap (rec [1..r]) (tuprange r (n-1))

-- generic set operations
pwdisj :: (Eq a) => [[a]] -> Bool
pwdisj [] = True
pwdisj (x:xs) = if (all (\y -> null(x `intersect` y)) xs) then (pwdisj xs) else False
	
pwrset :: [a] -> [[a]]
pwrset [] = [[]]; pwrset (x:xs) = (map ([x]++) (pwrset xs)) ++ (pwrset xs) 

-- remove subsets
rmsub :: (Eq a) => [[a]] -> [[a]]
rmsub [] = []
rmsub (x:xs) | (any (\y -> (x `intersect` y == x)) xs) = rmsub(xs) | otherwise = x:rmsub(xs) 

cmpsize :: [a] -> [a] -> Ordering
cmpsize s t = if(length(s) < length(t)) then LT else GT

-- substitution and evaluation
subst :: (Logic a) => L a -> Clause a -> L a
subst (And phi psi) s = And (subst phi s) (subst psi s)
subst (Or phi psi) s = Or (subst phi s) (subst psi s)
subst (Neg phi) s  = Neg (subst phi s)
subst T _ = T
subst F _ = F
subst phi (Clause (pos, neg))
  | elem phi neg = F
  | elem phi pos = T
		
eval :: L a -> Bool
eval T = True
eval F = False
eval (Neg phi)  = not (eval phi)
eval (Or phi psi) = (eval phi) || (eval psi)
eval (And phi psi) = (eval phi) && (eval psi)

-- dnf
allsat :: (Logic a) => L a -> [Clause a]
allsat phi = filter (\x -> eval (subst phi x)) (clauses (ma phi))
	
-- cnf
cnf :: (Logic a) => L a -> [Clause a]
cnf phi = map (\(Clause (x, y)) -> (Clause (y, x))) (allsat (Neg phi))

-- proof search
-- phi is provable iff all members of its CNF have a provable matching
-- also any matching is in general a cnf and all of its clauses must hold
provable :: (Logic a) => L a -> Bool
-- without tracing:
provable phi = all (\c -> any (all provable) ( match c)) (cnf phi)
-- uncomment the following to enable tracing
{-
provable phi =	let cnfphi = cnf phi; cnflen = length cnfphi;
				in	trace ("\n  rtp cnf: (" ++ (show cnflen) ++ ") " ++ show(map prettycl cnfphi) 
					++ "\n  \tof " ++ (pretty phi)) $ 
						all (\c -> any (all provable) (
					trace ("\n  rtp clause: " ++ (prettycl c) ++ " \n\tMatchings:" ++ (mpretty $ match c)) $ 
						match c)) (cnfphi) 
-}

-- clause to formula: avoids uneccessary Ts and Fs and prunes if possible
c2f ::  (Eq a) => Clause a -> L a
c2f (Clause ([], [])) = F
c2f (Clause (c, [])) = disj c
c2f (Clause ([], c)) = ndisj c
c2f (Clause (c, d)) = if (any (\x -> elem x c) d) then T else  disj $ nub (c ++ (map nneg d))


sat :: (Logic a) => L a -> Bool
sat phi = not $ provable $ neg phi

