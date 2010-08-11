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


-- generic code (no need for duplication)
------------------------------------------

(-->) :: (Logic f) => f -> f -> f
x --> y = (neg x) \/ y

(<-->) :: (Logic f) => f -> f -> f
x <--> y = (x --> y) /\ (y --> x)

-- disjunction of negation of elements
ndisj :: (Logic f) => [f] -> f
ndisj xs = disj (map neg xs)

-- create singleton lists containing disjunctions
disjlst :: (Logic f) => [f] -> [f]
disjlst ls = [disj ls]

-- negate a list
neglst :: (Logic f) => [f] -> [f]
neglst xs = map neg xs

-- generic: purely generic

-- avoids []->[[]], otherwise F matches F
listify :: [a] -> [[a]]
listify [] = []; listify x = [x]

-- length ordering on lists
cmpsize :: [a] -> [a] -> Ordering
cmpsize s t = if(length(s) < length(t)) then LT else GT

-- zip two lists together using a binary operator
zipbin :: (a -> a -> a) -> [a] -> [a] -> [a]
zipbin _ [] _ = [];	zipbin _ _ [] = [];
zipbin f (x:xs) (y:ys) = (f x y):(zipbin f xs ys)

-- given indices and a list find image
img :: [Int] -> [a] -> [a]
img inds ls = map (ls!!) inds 

-- map a list to indices from 0 -> length -1
toinds :: [a] -> [Int]
toinds [] = []; toinds xs = [0..(length xs)-1]


-- construct all integer n-tuples with elements from 1,..,r
tuprange :: Int -> Int -> [[Int]]
tuprange _ 0 = [[]]
tuprange r n = 
	let rec xs ys = map (\z -> z:ys) xs
	in	concatMap (rec [1..r]) (tuprange r (n-1))

	
-- generic: set operations

pwdisj :: (Eq a) => [[a]] -> Bool
pwdisj [] = True
pwdisj (x:xs) = if (all (\y -> null(x `intersect` y)) xs) then (pwdisj xs) else False
	
pwrset :: [a] -> [[a]]
pwrset [] = [[]]; pwrset (x:xs) = (map ([x]++) (pwrset xs)) ++ (pwrset xs) 

-- remove subsets
rmsub :: (Eq a) => [[a]] -> [[a]]
rmsub [] = []
rmsub (x:xs) | (any (\y -> (x `intersect` y == x)) xs) = rmsub(xs) | otherwise = x:rmsub(xs) 


-- generic: strippers and box collecting

-- strip a list
striplst :: (Strip f g) => [f] -> [g]
striplst ls = concatMap strip ls

onlyboxes :: (Logic f) => [f] -> [f]
onlyboxes ls = concatMap onlybox ls

cml :: (a -> [a]) -> [a] -> [a]
cml f ls = concatMap f ls

-- generic unary and binary provable

provable1 :: UnaryMatch f g => f -> Bool
provable1 phi = all (\c -> any (all provable) (matchu c)) (cnf phi) 

provable2 :: BinaryMatch f g h => f -> Bool
provable2 phi =
	let	bothprvble (as,bs) = (all provable as) && (all provable bs)
	in	all (\c -> any (\pair -> bothprvble pair) (matchb c)) (cnf phi) 

-- generic: main prover

-- all possible clauses
clauses :: (Logic f) => [f] -> [Clause f]
clauses [] = [Clause ([],[])]
clauses (a:as) = 
	let	padd c (Clause (p, n)) = Clause (c:p, n)
		nadd c (Clause (p, n)) = Clause (p, c:n)
	in	(map (padd a) (clauses as)) ++ (map (nadd a) (clauses as))
	
-- dnf
allsat :: (Logic f) => f -> [Clause f]
allsat phi = filter (\x -> (eval phi x)) (clauses (ma phi))

-- cnf
cnf :: (Logic f) => f -> [Clause f]
cnf phi = map (\(Clause (x, y)) -> (Clause (y, x))) (allsat (neg phi))

-- sat
sat :: (Logic f) => f -> Bool
sat phi = not $ provable $ neg phi
