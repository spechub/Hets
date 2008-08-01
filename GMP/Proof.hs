module Proof
--   ((-->), (<-->), (\/), (/\), true, false, box, dia, neg, var,  provable)
where

import Data.List (delete, intersect, nub)

-- data type for fomulas
data Form =  Var Int |
	    Not !Form |  -- ¬A
	    Box !Form | -- [] A
	    Conj !Form !Form  -- A/\B
	    deriving (Eq)

type Sequent =  [Form]     -- defines a sequent

-- pretty printing (sort of)
instance Show Form where
	show (Var p) = "p" ++ (show p)
	show (Not p) = "~" ++ show p
	show (Box p) = "[]" ++ show p
	show (Conj p q) = "(" ++ show p ++ " & " ++ show q ++ ")"

-- syntactic sugar
p = Var 0
q = Var 1
r = Var 2

(-->) :: Form -> Form -> Form
infixr 5 -->
-- p --> q = Disj (Not p) q
p --> q = Not (Conj p (Not q))

(<-->) :: Form -> Form -> Form
infixr 4 <-->
p <--> q = Not (Conj (Not ( Conj p q)) (Not(Conj (Not p) (Not q))))

box :: Form -> Form
box p = Box p

dia :: Form -> Form
dia p = Not( Box ( Not p ) )

(/\) :: Form -> Form -> Form
infix 7 /\
p /\ q = Conj p q

(\/) :: Form -> Form -> Form
infix 6 \/
p \/ q = neg ( (neg p) /\ (neg q))

neg :: Form -> Form
neg p = Not p

false :: Form
false = (Var 0) /\ (Not (Var 0))

true :: Form
true = neg false

var :: Int -> Form
var n = Var n

-- the rank of a modal formula
rank :: Form -> Int
rank (Box p) = 1 + (rank p)
rank (Conj p q) =  (max (rank p) (rank q))
rank (Not p) = rank p
rank (Var p) = 0

-- expand applies all sequent rules that do not induce branching
expand :: Sequent -> Sequent
expand s | seq s $ False = undefined -- force strictness
expand [] = []
expand ((Not (Not p)):as) = expand  (p:as)
expand ((Not (Conj p q)):as) = expand ((Not p):(Not q):as)
expand (a:as) = a:(expand as)

----------------------------------------------------------------------------------------------------

--Inference Rules
-- map a sequent the list of all lists of all premises that derive
-- the sequent. Note that a premise is a list of sequents:
-- * to prove Gamma, A /\ B we need both Gamma, A and Gamma, B as premises.
-- * to prove Gamma, neg(A /\ B), we need Gamma, neg A, neg B as premise.
-- * to prove A, neg A, Gamma we need no premises
-- So a premise is a list of sequents, and the list of all possible
-- premises therefore has type [[ Sequent ]]

-- the functions below compute the list of all possible premises
-- that allow to derive a given sequent using the rule that
-- lends its name to the function.
axiom :: Sequent -> [[Sequent]]
-- faster to check for atomic axioms
-- axiom1 xs = [ []  | p <- xs, (Not q) <- xs, p==q]
axiom xs = nub [ []  | (Var n) <- xs, (Not (Var m)) <- xs, m==n]

negI :: Sequent -> [[Sequent]]
negI  xs = [ [(p: delete f xs)] | f@(Not(Not p)) <- xs]

negConj :: Sequent -> [[Sequent]]
negConj (as) = [[( (Not(p)): (Not(q)) : delete f as )]| f@(Not(Conj p q)) <- as]


-- two variants here: use @-patterns or ``plain'' recursion.
conj :: Sequent -> [[ Sequent ]]
conj s | seq s $ False = undefined -- force strictness
conj (as) = [ [ (p: delete f as) , ( q: delete f as )] | f@(Conj p q ) <- as]

boxI :: Sequent -> [[Sequent]]
boxI (xs) = let as = [ (Not p) | (Not(Box p)) <- xs]
            in [ [ p:as] | (Box p) <- xs ]  ++
						   [ [ (Not q):delete g xs] | g@(Not (Box q)) <- xs ] -- T rule
tRule :: Sequent -> [[ Sequent ]]
tRule (xs) = [ [ (Not p):delete f xs] | f@(Not (Box p)) <- xs ] -- T rule

-- collect all possible premises, i.e. the union of the possible
-- premises taken over the set of all rules in one to  get the
-- recursion off the ground.

-- CAVEAT: the order of axioms /rules has a HUGE impact on performance.
allRules :: Sequent -> [[Sequent]]
-- this is as good as it gets if we apply the individual rules
-- message for the afterworld: if you want to find proofs quickly,
-- first look at the rules that induce branching.
-- allRules s =   (axiom1 s) ++ (axiom2 s) ++ (boxI s) ++ (conj s) ++ (negDisj s) ++ (negI s) ++  (negConj s) ++  (disj s)


-- we can do slightly better if we apply all rules that do not
-- induce branching in one single step.
allRules s = let t = expand s in (axiom $ t) ++ (boxI $ t) ++ (conj $ t) -- ++ (tRule  t)


-- A sequent is provable iff there exists a set of premises that
-- prove the sequent such that all elements in the list of premises are
-- themselves provable.
sprovable :: Sequent -> Bool
sprovable s | seq s $ False = undefined -- force strictness
sprovable s = any  (\p -> (all sprovable p)) (allRules s)

-- specialisatino to formulas
provable :: Form -> Bool
provable p = sprovable [ p ]

--  test cases:
dp1 =   (neg (neg p)) \/ ((neg (neg q)) \/ r)   -- not provable

dp2 = box p \/ neg(box p) -- provable
dp3 = box p \/ neg(box(neg(neg p))) -- provable

dp4 = neg( neg(box p /\ neg(box p)) --> (box q /\ box p) /\ neg(box q))
dp5 = neg( neg(box p /\ neg(box p)) --> (box q /\ box p) /\ dia(neg q))

dp6 = (box p) /\ (dia q) --> (dia (p /\ q))  -- true?
dp7 = (box (dia (box p))) --> (dia (box (neg p)))  -- false?

level :: Int -> [Form]
level 0 = [var 0, var 1, neg $ var 0, neg $ var 1 ]
level n = let pbox = map box [ x | i <- [0 .. (n-1)], x <- (level i)]
              nbox = map (neg . box)  [ x | i <- [0 .. (n-1)], x <- (level i)]
          in
					pbox ++ nbox ++ [ p /\ q | p <- pbox, q <- nbox] ++ [neg (p /\ q) | p <- pbox, q <- nbox ]

tforms :: [ (Sequent, Sequent) ]
tforms = [ ([neg a, neg $ box a, b ], [neg $ box a, b])  | a <- level 2, b <- level 2]

ttest :: [ (Sequent, Sequent) ] -> String
ttest [] = []
ttest ( (s1, s2):as ) =
  let s1p = (sprovable s1) ;
	    s2p = (sprovable s2)
  in if (s1p /= s2p) then "GOTCHA: " ++ (show s1) ++ (show s2) ++ "<"
	                   else "*" ++ (ttest as)
