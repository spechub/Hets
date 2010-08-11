{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
// -------------------------------
// Matchings for logics & bin ops
// -------------------------------

BEGIN_MATCHINGS

BEGIN_K_MATCHING
instance UnaryMatch L_ID_ L_PID_ where
	matchu (Clause (pl,nl)) =
		let (nls,pls) = (map neg (striplst nl), striplst pl)
		in (map disjlst (map (\x -> x:nls) pls))	
END_K_MATCHING

BEGIN_HM_MATCHING
instance UnaryMatch L_ID_ L_PID_ where
	matchu (Clause (pl,nl)) =
	  let isag a (_UNOP_ ind x) = (ind == a); -- is it agent a?
		    isag a _ = False;
	      ag (_UNOP_ ind x) = Just ind; -- find the agent
				ag _ = Nothing;
	      ags = nub $ catMaybes (map ag (pl ++ nl)); -- the set of agents we have
	      aglits = map (\x -> (filter (isag x) pl, filter (isag x) nl)) ags;
	      -- this is a list of pairs (pl, nl) for each agent
	      strlits  = map (\(x, y) -> ((striplst x), map neg (striplst y))) aglits;
	      -- the same with boxes stripped
	      comb (pls, nls) = map disjlst (map (\x -> x:nls) pls);
	      -- turn a combination pls/nls into a list of formulas
	      fllist = map comb strlits;
	      -- a list of lists consisting of formulas
	  in concat fllist
END_HM_MATCHING

BEGIN_KD_MATCHING
instance UnaryMatch L_ID_ L_PID_ where
	matchu (Clause (pl,nl)) = 
		let	(nls,pls) = (map neg (striplst nl), striplst pl)
			xnls = listify nls
		in map disjlst ((map (\x -> x:nls) pls) ++ xnls)
END_KD_MATCHING

BEGIN_C_MATCHING
instance UnaryMatch L_ID_ L_PID_ where
	matchu (Clause (pls,nls)) =
		let	pNs = concatMap stripFull_ID_ pls
			(bnls,bpls) = (onlyboxes nls, onlyboxes pls)
			allneg = map neg (striplst nls)
			xallneg = listify allneg
		in map disjlst ((map (pNs++) (cmatch_ID_ bpls bnls)) ++ xallneg) 

agents_ID_ :: Int; agents_ID_ = 10

stripFull_ID_ :: L_ID_ -> [L_PID_]
stripFull_ID_ (_UNOP_ ints phi) | (ints == [1..agents_ID_]) = [phi] | otherwise = []
stripFull_ID_ _ = [];

	
-- form 'pw disj subsets of +ve lit' parts of matching clause
cmatch_ID_ :: [L_ID_] -> [L_ID_] -> [[L_PID_]]
cmatch_ID_ [] _ = []
cmatch_ID_ ((_UNOP_ pset pphi):pls) nls =
	let	subnls = filter (\(_UNOP_ s _) -> ((s `intersect` pset)==s)) nls
		sublsts = nub $ map (\(_UNOP_ s _) -> s) subnls
		maxpwdjs = rmsub $ sortBy cmpsize (filter (pwdisj) (pwrset sublsts))
 		negmats = map (neglst) (map (striplst) (concatMap (ch_ID_ subnls) maxpwdjs)) 
	in	(map ([pphi]++) negmats) ++ (cmatch_ID_ pls nls)
	
-- given lits and pairwise disj lists, form pairwise disj lit lists
ch_ID_ :: [L_ID_] -> [[Int]] -> [[L_ID_]]
ch_ID_ _ [] = [[]]
ch_ID_ lits allsets@(set:sets) =
	let ls = filter (\(_UNOP_ t _) -> set==t) lits
	in	if null(ls) then [] else
		(map ([head ls]++) (ch_ID_ lits sets)) ++ (ch_ID_ (lits\\[head ls]) allsets)
END_C_MATCHING

BEGIN_P_MATCHING
instance UnaryMatch L_ID_ L_PID_ where
	matchu (Clause (pls,nls)) =
			let	(bpls,bnls) = (onlyboxes pls, onlyboxes nls)
				allcls = [Clause(ps,ns) | 
					ps <- (pwrset bpls), ns <- (pwrset bnls)] \\ [Clause([],[])]
				xrats xs = map (\(_UNOP_ k _) -> k) xs
				bnd (Clause(ps,ns)) = pmlbnd ((xrats ps),(xrats ns))
				tups cl@(Clause(ps,ns)) = 
					[(pts,nts,k)|	pts <- (tuprange (bnd cl) (length ps)), 
									nts <- (tuprange (bnd cl) (length ns)),
									k <- [-(bnd cl)..(bnd cl)]]
				sctups cl = filter (pmlsc_ID_ cl) (tups cl)
				-- find minimal elts of those tupes satisfying the side condition
				leq ::  ([Int],[Int], Int) ->  ([Int],[Int], Int) -> Bool
				leq (p1, n1, k1) (p2, n2, k2) = (k1 == k2) && (and (( map (\(x, y) -> x <= y) (( zip p1 p2) ++ (zip  n1 n2)))))
				geq ::  ([Int],[Int], Int) ->  ([Int],[Int], Int) -> Bool
				geq (p1, n1, k1) (p2, n2, k2) = (k1 == k2) && (and (( map (\(x, y) -> x >= y) (( zip p1 p2) ++ (zip  n1 n2)))))
				ftups :: [([Int], [Int], Int)] -> [([Int], [Int], Int)] -> [([Int], [Int], Int)]
				ftups [] bs = bs
				ftups (a:as) bs
					| any (\x -> geq x a) bs = ftups as bs
					| otherwise = a:(filter (\x -> not (leq x a)) bs)
				clmatch cl = map (pmlcnf_ID_ cl) (ftups (sctups cl) [] )
				-- clmatch cl = map (pmlcnf_ID_ cl) (sctups cl) 
			in	nub $ concatMap clmatch allcls

pmlcnf_ID_ :: Clause L_ID_ -> ([Int],[Int], Int) -> [L_PID_]
pmlcnf_ID_ (Clause(pls,nls)) (prs,nrs,k) =
	let	(pinds,ninds) = (toinds prs,toinds nrs)
		(spls,snls) = (striplst pls,striplst nls)
		allinds = [(ps,ns) | ps <- (pwrset pinds), ns <- (pwrset ninds)]
		cnfinds = filter (\(ps,ns) -> (sum$img ps prs) - (sum$img ns nrs) < k) allinds
		getJ (ps,ns) = (img ps spls) ++ (img ns snls)
		getnJ (ps,ns) = (img (pinds \\ ps) spls) ++ (img (ninds \\ ns) snls)
	in	map (\rs -> ndisj(getJ rs) \/ disj(getnJ rs)) cnfinds

pmlsc_ID_ :: Clause L_ID_ -> ([Int],[Int], Int) -> Bool
pmlsc_ID_ (Clause(pls,nls)) (pints,nints,k) =
	let	(rpints,rnints) = (map fromIntegral pints,map fromIntegral nints)
		psum = sum $ zipbin (*) rpints (map (\(_UNOP_ x _)->fromRational(x)) pls)
		nsum = sum $ zipbin (*) rnints (map (\(_UNOP_ x _)-> fromRational(-x)) nls)
	in	if null(pints) 	then (psum + nsum < fromIntegral(k))
						else (psum + nsum <= fromIntegral(k))

pmlbnd :: ([Rational],[Rational]) -> Int
-- pmlbnd _ = 1
pmlbnd (rps,rns) = 
	let	n = (length rps) + (length rns)
		toints rs = concatMap (\r -> [numerator r,denominator r]) rs
		allints = (toints rps) ++ (toints rns)
		logint n = ceiling(logBase 2 (1 + n))
		logsum = sum $ map (\n -> logint (fromIntegral(n))) allints
	in	20*n*n*(1+n) + 10*n*n*logsum
END_P_MATCHING


BEGIN_G_MATCHING
instance UnaryMatch L_ID_ L_PID_ where
	matchu (Clause (pls,nls)) =
		let	(bpls,bnls) = (onlyboxes pls, onlyboxes nls)
			allcls = [Clause(ps,ns) | 
				ps <- (pwrset bpls), ns <- (pwrset bnls)] \\ [Clause([],[])]
			xints xs = map (\(_UNOP_ k _) -> k) xs
			bnd (Clause(ps,ns)) = gmlbnd_ID_ ((xints ps),(xints ns))
			tups cl@(Clause(ps,ns)) = 
				[(pts,nts)|	pts <- (tuprange (bnd cl) (length ps)), 
							nts <- (tuprange (bnd cl) (length ns))]
			sctups cl = filter (gmlsc_ID_ cl) (tups cl)
			-- find minimal elts of those tupes satisfying the side condition
			leq ::  ([Int],[Int]) ->  ([Int],[Int]) -> Bool
			leq (p1, n1) (p2, n2) =  (and (( map (\(x, y) -> x <= y) (( zip p1 p2) ++ (zip  n1 n2)))))
			geq ::  ([Int],[Int]) ->  ([Int],[Int]) -> Bool
			geq (p1, n1) (p2, n2) =  (and (( map (\(x, y) -> x >= y) (( zip p1 p2) ++ (zip  n1 n2)))))
			ftups :: [([Int], [Int])] -> [([Int], [Int])] -> [([Int], [Int])]
			ftups [] bs = bs
			ftups (a:as) bs
				| any (\x -> geq x a) bs = ftups as bs
				| otherwise = a:(filter (\x -> not (leq x a)) bs)
			clmatch cl = map (gmlcnf_ID_ cl) (ftups (sctups cl) [] )
			-- clmatch cl = map (gmlcnf_ID_ cl) (sctups cl) 
		in	nub $ concatMap clmatch allcls

-- GML CNF: given clause & tuple output cnf
-- e.g. given clause (pos as,neg as), (pos rs,neg rs), 
-- find all combinations whose sum is less than 0
gmlcnf_ID_ :: Clause L_ID_ -> ([Int],[Int]) -> [L_PID_]
gmlcnf_ID_ (Clause(pls,nls)) (prs,nrs) =
	let	(pinds,ninds) = (toinds prs,toinds nrs)
		(spls,snls) = (striplst pls,striplst nls)
		allinds = [(ps,ns) | ps <- (pwrset pinds), ns <- (pwrset ninds)]
		cnfinds = filter (\(ps,ns) -> (sum$img ps prs)<(sum$img ns nrs)) allinds
		getJ (ps,ns) = (img ps spls) ++ (img ns snls)
		getnJ (ps,ns) = (img (pinds \\ ps) spls) ++ (img (ninds \\ ns) snls)
	in	map (\rs -> ndisj(getJ rs) \/ disj(getnJ rs)) cnfinds

-- GML side condition
gmlsc_ID_ :: Clause L_ID_ -> ([Int],[Int]) -> Bool
gmlsc_ID_ (Clause(pls,nls)) (pints,nints) =
	let	psum = sum $ zipbin (*) pints (map (\(_UNOP_ k _)->fromIntegral(k)) pls)
		nsum = sum $ zipbin (*) nints (map (\(_UNOP_ k _)->1+fromIntegral(k)) nls)
	in	nsum >= 1 + psum
	
-- GML bound on integer magnitude
gmlbnd_ID_ :: ([Int],[Int]) -> Int
-- gmlbnd_ID_ _ = 1
gmlbnd_ID_ (kps,kns) = 
	let	n = (length kps) + (length kns)
		logint k x = ceiling $ logBase 2 (k + x)
		logsum ls k = sum $ map (\x -> logint k (fromIntegral(x))) ls	
	in	12*n*(1+n) + 6*n*((logsum kps 1) + (logsum kns 2))
END_G_MATCHING

BEGIN_COPROD_MATCHING
instance BinaryMatch L_ID_ L_CID1_ L_CID2_ where
	matchb (Clause (pls,nls)) = 
		let	f1 = (disj $ striplst pls) \/ (ndisj $ striplst nls)
			f2 = (disj $ striplst pls) \/ (ndisj $ striplst nls)
		in	[([f1],[f2])]
END_COPROD_MATCHING


BEGIN_COND_MATCHING
instance BinaryMatch L_ID_ L_CID1_ L_CID2_ where
	matchb (Clause([],[])) = []
	matchb (Clause(pls,nls)) =
		let	alpha = head $ (stripCondL_ID_ $ head (pls ++ nls))
			xcls xs = partition (\(_BINOP_ a b) -> (a == alpha)) xs
			((cpls,pls2),(cnls,nls2)) = (xcls $ onlyboxes pls,xcls $ onlyboxes nls)
			fs = (disj $ striplst cpls) \/ (ndisj $ striplst cnls)
		in	([],[fs]):(matchb (Clause(pls2,nls2)))

stripCondL_ID_ :: (Strip L_ID_ L_CID1_) => L_ID_ -> [L_CID1_]
stripCondL_ID_ xs = strip xs
END_COND_MATCHING

BEGIN_FUSE_MATCHING
instance BinaryMatch L_ID_ L_CID1_ L_CID2_ where
	matchb (Clause (pls,nls)) = 
		let	(posPi1,negPi1) = (concatMap stripFus1__ID_ pls,concatMap stripFus1__ID_ nls)
			(posPi2,negPi2) = (concatMap stripFus2__ID_ pls,concatMap stripFus2__ID_ nls)
			fromLits (ps,ns) = [(disj ps) \/ (ndisj ns)]
		in	[(fromLits (posPi1,negPi1),[]),([],fromLits (posPi2,negPi2))]

stripFus1__ID_ :: (Strip L_ID_ L_CID1_) => L_ID_ -> [L_CID1_]
stripFus1__ID_ xs = strip xs

stripFus2__ID_ :: (Strip L_ID_ L_CID2_) => L_ID_ -> [L_CID2_]
stripFus2__ID_ xs = strip xs
END_FUSE_MATCHING

END_MATCHINGS

// -------------------------------
// 'Provable' code for logics & ops
// -------------------------------

BEGIN_PROVABLES

BEGIN_UNARY_PROVABLE
	provable phi = provable1 phi
END_UNARY_PROVABLE

BEGIN_BINARY_PROVABLE
	provable phi = provable2 phi
END_BINARY_PROVABLE


END_PROVABLES

// --------------------
// Logic class instance
// --------------------

BEGIN_LOGIC
instance Logic L_N_ where
	ff = F_N_; tt = T_N_;
	x = Atom_N_ 1; y = Atom_N_ 2; z = Atom_N_ 3;
	neg F_N_ = T_N_; neg T_N_ = F_N_; neg x = Neg_N_ x
	x \/ y = Or_N_ x y
	x /\ y = And_N_ x y
	_ONLYBOX_
	disj [] = F_N_; disj [a] = a; disj (a:as) = Or_N_ a (disj as)
	ma (And_N_ phi psi) = (ma phi) `union` (ma psi)
	ma (Or_N_ phi psi) = (ma phi) `union` (ma psi)
	ma (Neg_N_ phi) = ma phi
	ma T_N_ = []; ma F_N_ = []; ma (Atom_N_ x) = [Atom_N_ x]
	ma x = [x]
	eval (And_N_ phi psi) s = (eval phi s) && (eval psi s)
	eval (Or_N_ phi psi) s = (eval phi s) || (eval psi s)
	eval (Neg_N_ phi) s  = not (eval phi s)
	eval T_N_ s = True; eval F_N_ s = False
	eval phi (Clause (pos, neg))
	  | elem phi neg = False
	  | elem phi pos = True
	_PROVABLE_
END_LOGIC

BEGIN_ONLYBOXS

BEGIN_BASIC_ONLYBOX
	onlybox (_BOXED_) = [_BOXED_]; onlybox _ = []
END_BASIC_ONLYBOX

BEGIN_COPROD_ONLYBOX
	onlybox (_BOXED_) = [_BOXED_]; onlybox _ = []
END_COPROD_ONLYBOX

BEGIN_COND_ONLYBOX
	onlybox (_BOXED_) = [_BOXED_]; onlybox _ = []
END_COND_ONLYBOX

BEGIN_FUSE_ONLYBOX
	onlybox (Pi1__ID_ x) = [Pi1__ID_ x]; onlybox _ = []
	onlybox (Pi2__ID_ x) = [Pi2__ID_ x]; onlybox _ = []
END_FUSE_ONLYBOX

END_ONLYBOXS

// --------------------
// Strip class instances
// --------------------

BEGIN_STRIPPERS

BEGIN_UNARY_STRIP
instance Strip _FROM_ _TO_ where
	strip (_UNOP_ x) = [x]; strip _ = [];
END_UNARY_STRIP

BEGIN_COND_STRIP
instance Strip _FROM_ _TO1_ where
	strip (_BINOP_ x _) = [x]; strip _ = [];
	
instance Strip _FROM_ _TO2_ where
	strip (_BINOP_ _ y) = [y]; strip _ = [];
END_COND_STRIP

BEGIN_COPROD_STRIP
instance Strip _FROM_ _TO1_ where
	strip (_BINOP_ x _) = [x]; strip _ = [];
	
instance Strip _FROM_ _TO2_ where
	strip (_BINOP_ _ y) = [y]; strip _ = [];
END_COPROD_STRIP

BEGIN_FUSE_STRIP
instance Strip _FROM_ _TO1_ where
	strip (_UNOP1_ x) = [x]; strip _ = [];
	
instance Strip _FROM_ _TO2_ where
	strip (_UNOP2_ x) = [y]; strip _ = [];
END_FUSE_STRIP

END_STRIPPERS
