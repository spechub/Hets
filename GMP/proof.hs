import List (delete, intersect)

-- data type for fomulas
data Form = Atom String | 
	    Not Form |  -- ¬A
	    Box Form | -- [] A 
	    F | -- False 
	    Conj Form Form -- A/\B
	    deriving Eq 

type Sequent = [Form]     -- defines a sequent 

-- pretty printing (sort of)
instance Show Form where 
	show (Atom p) = p
	show (Not p) = "~" ++ show p 
	show (Box p) = "[]" ++ show p
	show F = "F"
	show (Conj p q) = "(" ++ show p ++ " & " ++ show q ++ ")"

-- syntactic sugar
p = Atom "p" 
q = Atom "q" 
r = Atom "r" 

(-->) :: Form -> Form -> Form 
infixr 5 -->
p --> q = Not ( Conj p (Not q))

(<-->) :: Form -> Form -> Form 
infixr 4 <-->
p <--> q = Not (Conj (Not ( Conj p q)) (Not(Conj (Not p) (Not q))))

box :: Form -> Form
box p = Box p 

diamond :: Form -> Form 
diamond p = Not( Box ( Not p ) ) 

(/\) :: Form -> Form -> Form
infix 7 /\
p /\ q = Conj p q

(\/) :: Form -> Form -> Form
infix 6 \/
p \/ q = Not (Conj (Not p) (Not q))

neg :: Form -> Form
neg p = Not p

----------------------------------------------------------------------------------------------------

--Inference Rules 
-- map a sequent the list of all lists of all premises that derive
-- the sequent. Note that a premise is a list of sequents:
-- * to proove Gamma, A /\ B we need both Gamma, A and Gamma, B as premises.
-- * to prove Gamma, neg(A /\ B), we need Gamma, neg A, neg B as premise.
-- * to proove A, neg A, Gamma we need no premises
-- So a premise is a list of sequents, and the list of all possible
-- premises therefore has type [[ Sequent ]]

-- the functions below compute the list of all possible premises
-- that allow to derive a given sequent using the rule that
-- lends its name to the function.
axiom1 :: Sequent -> [[Sequent]]
axiom1 xs = [ []  | f@(p) <- xs, g@(Not(q)) <- xs, p==q]

axiom2 :: Sequent -> [[Sequent]]
axiom2 xs  = [ [] | (Not F) `elem` xs ]
				
negI :: Sequent -> [[Sequent]] 
negI  xs = [ [(p: delete f xs)] | f@(Not(Not p)) <- xs]

negConj :: Sequent -> [[Sequent]] 
negConj as = [[( (Not(p)): (Not(q)) : delete f as )]| f@(Not(Conj p q)) <- as]

conj :: Sequent -> [[Sequent]]
conj (as) = [ [ (p: delete f as) , ( q: delete f as )] | f@(Conj p q ) <- as] 

boxI :: Sequent -> [[Sequent]] 
boxI (xs) = let as = [ (Not p) | f@(Not(Box p)) <- xs] in [ [ p:as] | f@(Box p) <- xs ]

-- collect all possible premises, i.e. the union of the possible
-- premises taken over the set of all rules in one to  get the
-- recursion off the ground.
allRules :: Sequent -> [[Sequent]]
allRules s =  (axiom1 s) ++ (axiom2 s) ++ (negI s) ++  (negConj s) ++  (conj s) ++  (boxI s)

-- A sequent is provable iff there exists a set of premises that
-- prove the sequent such that all elements in the list of premises are
-- themselves provable.
provable :: Sequent -> Bool
provable s = any (\p -> (all provable p)) (allRules s)

--  test cases:
dp1 ::  Sequent
dp1 =  [ (neg (neg p)), (neg (neg q)), r  ] -- not provable

dp2 = [box p, neg(box p)] -- provable
dp3 = [box p, neg(box(neg(neg p)))] -- provable

dp4 = [neg( neg(box p /\ neg(box p)) --> (box q /\ box p) /\ neg(box q))]
dp5 = [neg( neg(box p /\ neg(box p)) --> (box q /\ box p) /\ diamond(neg q))]

dp6 = [ (box p) /\ (diamond q) --> (diamond (p /\ q)) ] -- true?
dp7 = [ (box (diamond (box p))) --> (diamond (box (neg p))) ] -- false?

