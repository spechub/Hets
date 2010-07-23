{- |
Module      :  $Header$
Description :  folding function for propositional formulas extended with QBFs
Copyright   :  (c) Jonathan von Schroeder, DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  <jonathan.von_schroeder@dfki.de>
Stability   :  provisional
Portability :  portable

folding and simplification of propositional formulas

-}

module QBF.Tools where

import Common.Id
import QBF.AS_BASIC_QBF

import qualified Data.Map as Map

import Data.List (nub, (\\))

import qualified Data.Set as Set

data FoldRecord a = FoldRecord
  { foldNegation :: a -> Range -> a
  , foldConjunction :: [a] -> Range -> a
  , foldDisjunction :: [a] -> Range -> a
  , foldImplication :: a -> a -> Range -> a
  , foldEquivalence :: a -> a -> Range -> a
  , foldTrueAtom :: Range -> a
  , foldFalseAtom :: Range -> a
  , foldPredication :: Token -> a
  , foldForAll :: [Token] -> a -> Range -> a
  , foldExists :: [Token] -> a -> Range -> a }

foldFormula :: FoldRecord a -> FORMULA -> a
foldFormula r frm = case frm of
   Negation f n -> foldNegation r (foldFormula r f) n
   Conjunction xs n -> foldConjunction r (map (foldFormula r) xs) n
   Disjunction xs n -> foldDisjunction r (map (foldFormula r) xs) n
   Implication x y n -> foldImplication r (foldFormula r x) (foldFormula r y) n
   Equivalence x y n -> foldEquivalence r (foldFormula r x) (foldFormula r y) n
   TrueAtom n -> foldTrueAtom r n
   FalseAtom n -> foldFalseAtom r n
   Predication x -> foldPredication r x
   ForAll xs f n -> foldForAll r xs (foldFormula r f) n
   Exists xs f n -> foldExists r xs (foldFormula r f) n

mapRecord :: FoldRecord FORMULA
mapRecord = FoldRecord
  { foldNegation = Negation
  , foldConjunction = Conjunction
  , foldDisjunction = Disjunction
  , foldImplication = Implication
  , foldEquivalence = Equivalence
  , foldTrueAtom = TrueAtom
  , foldFalseAtom = FalseAtom
  , foldPredication = Predication
  , foldForAll = ForAll
  , foldExists = Exists }

isNeg :: FORMULA -> Bool
isNeg f = case f of
  Negation _ _ -> True
  ForAll _ x _ -> isNeg x
  Exists _ x _ -> isNeg x
  _ -> False

isQuantified :: FORMULA -> Bool
isQuantified f = case f of
  FalseAtom _ -> False
  TrueAtom _ -> False
  Predication _ -> False
  Negation f1 _ -> isQuantified f1
  Conjunction xs _ -> any isQuantified xs
  Disjunction xs _ -> any isQuantified xs
  Implication x y _ -> any isQuantified [x, y]
  Equivalence x y _ -> any isQuantified [x, y]
  ForAll _ _ _ -> True
  Exists _ _ _ -> True

getLits :: Set.Set FORMULA -> Set.Set FORMULA
getLits = Set.fold (\ f -> case f of
  Negation x _ -> Set.insert x
  ForAll ts f1 n -> case f1 of
    Negation x _ -> Set.insert (ForAll ts x n)
    _ -> Set.insert (ForAll ts f n)
  _ -> Set.insert f) Set.empty

bothLits :: Set.Set FORMULA -> Bool
bothLits fs = let
  (ns, ps) = Set.partition isNeg fs
  in not $ Set.null $ Set.intersection (getLits ns) (getLits ps)

getConj :: FORMULA -> [FORMULA]
getConj f = case f of
  Conjunction xs _ -> xs
  _ -> [f]

getDisj :: FORMULA -> [FORMULA]
getDisj f = case f of
  Disjunction xs _ -> xs
  _ -> [f]

flatConj :: [FORMULA] -> Set.Set FORMULA
flatConj = Set.fromList
  . concatMap (\ f -> case f of
      TrueAtom _ -> []
      Conjunction fs _ -> fs
      _ -> [f])

mkConj :: [FORMULA] -> Range -> FORMULA
mkConj fs n = let s = flatConj fs in
  if Set.member (FalseAtom nullRange) s || bothLits s then FalseAtom n else
  case Set.toList s of
    [] -> TrueAtom n
    [x] -> x
    ls -> Conjunction (map (flip mkDisj n . Set.toList)
      $ foldr ((\ l ll ->
        if any (`Set.isSubsetOf` l) ll then ll else
          l : filter (not . Set.isSubsetOf l) ll)
          . Set.fromList . getConj)
        [] ls) n

flatDisj :: [FORMULA] -> Set.Set FORMULA
flatDisj = Set.fromList
  . concatMap (\ f -> case f of
      FalseAtom _ -> []
      Disjunction fs _ -> fs
      _ -> [f])

mkDisj :: [FORMULA] -> Range -> FORMULA
mkDisj fs n = let s = flatDisj fs in
  if Set.member (TrueAtom nullRange) s || bothLits s then TrueAtom n else
  case Set.toList s of
    [] -> FalseAtom n
    [x] -> x
    ls -> Disjunction (map (flip mkConj n . Set.toList)
      $ foldr ((\ l ll ->
        if any (`Set.isSubsetOf` l) ll then ll else
          l : filter (not . Set.isSubsetOf l) ll)
          . Set.fromList . getConj)
      [] ls) n

simplify :: FORMULA -> FORMULA
simplify = foldFormula mapRecord
  { foldNegation = \ f n -> case f of
    TrueAtom p -> FalseAtom p
    FalseAtom p -> TrueAtom p
    Negation g _ -> g
    s -> Negation s n
  , foldConjunction = mkConj
  , foldDisjunction = mkDisj
  , foldImplication = \ x y n -> case x of
    FalseAtom p -> TrueAtom p
    _ -> if x == y then TrueAtom n else case x of
           TrueAtom _ -> y
           FalseAtom _ -> TrueAtom n
           Negation z _ | z == y -> x
           _ -> case y of
             Negation z _ | z == x -> x
             _ -> Implication x y n
  , foldEquivalence = \ x y n -> case compare x y of
    LT -> case y of
      Negation z _ | x == z -> FalseAtom n
      _ -> Equivalence x y n
    EQ -> TrueAtom n
    GT -> case x of
      Negation z _ | z == y -> FalseAtom n
      _ -> Equivalence y x n }

elimEquiv :: FORMULA -> FORMULA
elimEquiv = foldFormula mapRecord
  { foldEquivalence = \ x y n ->
    Conjunction [Implication x y n, Implication y x n] n }

elimImpl :: FORMULA -> FORMULA
elimImpl = foldFormula mapRecord
  { foldImplication = \ x y n ->
    Disjunction [Negation x n, y] n }

negForm :: Range -> FORMULA -> FORMULA
negForm r frm = case frm of
  Negation f _ -> f
  Conjunction xs n -> Disjunction (map (negForm r) xs) n
  Disjunction xs n -> Conjunction (map (negForm r) xs) n
  TrueAtom n -> FalseAtom n
  FalseAtom n -> TrueAtom n
  ForAll ts f n -> ForAll ts (negForm r f) n
  Exists ts f n -> Exists ts (negForm r f) n
  _ -> Negation frm r

moveNegIn :: FORMULA -> FORMULA
moveNegIn frm = case frm of
  Negation f n -> negForm n f
  Conjunction xs n -> Conjunction (map moveNegIn xs) n
  Disjunction xs n -> Disjunction (map moveNegIn xs) n
  ForAll ts f n -> ForAll ts (moveNegIn f) n
  Exists ts f n -> Exists ts (moveNegIn f) n
  _ -> frm

distributeAndOverOr :: FORMULA -> FORMULA
distributeAndOverOr f = case f of
  Conjunction xs n -> mkConj (map distributeAndOverOr xs) n
  Disjunction xs n -> if all isPrimForm xs then mkDisj xs n else
    distributeAndOverOr
    $ mkConj (map (`mkDisj` n) . combine $ map getConj xs) n
  ForAll ts x n -> ForAll ts (distributeAndOverOr x) n
  Exists ts x n -> Exists ts (distributeAndOverOr x) n
  _ -> f

{- note: won't work fully if the formula is quantified because
it can't distribute through quantifications -}
cnf :: FORMULA -> FORMULA
cnf = distributeAndOverOr . moveNegIn . elimImpl . elimEquiv

distributeOrOverAnd :: FORMULA -> FORMULA
distributeOrOverAnd f = case f of
  Disjunction xs n -> mkDisj (map distributeOrOverAnd xs) n
  Conjunction xs n -> if all isPrimForm xs then mkConj xs n else
    distributeOrOverAnd
    $ mkDisj (map (`mkConj` n) . combine $ map getDisj xs) n
  _ -> f

{- note: won't work fully if the formula is quantified because
it can't distribute through quantifications -}
dnf :: FORMULA -> FORMULA
dnf = distributeOrOverAnd . moveNegIn . elimImpl . elimEquiv

combine :: [[a]] -> [[a]]
combine l = case l of
  [] -> [[]]
  h : t -> concatMap (flip map h . flip (:)) (combine t)

containsAtoms :: FORMULA -> (Bool, Bool)
containsAtoms f = let
    join (x, y) (x1, y1) = (x && x1, y && y1)
  in
    case f of
      (Negation x _ ) -> containsAtoms x
      (Conjunction fs _ ) -> foldl join (False, False) (map containsAtoms fs)
      (Disjunction fs _ ) -> foldl join (False, False) (map containsAtoms fs)
      (Implication f1 f2 _ ) -> join (containsAtoms f1) (containsAtoms f2)
      (Equivalence f1 f2 _ ) -> join (containsAtoms f1) (containsAtoms f2)
      (TrueAtom _) -> (True, False)
      (FalseAtom _) -> (False, True)
      (Predication _) -> (False, False)
      (ForAll _ x _) -> containsAtoms x
      (Exists _ x _) -> containsAtoms x

getVars :: FORMULA -> [Token]
getVars (Negation x _) = getVars x
getVars (Conjunction xs _) = nub (concatMap getVars xs)
getVars (Disjunction xs _) = nub (concatMap getVars xs)
getVars (Implication x1 x2 _) = nub (getVars x1 ++ getVars x2)
getVars (Equivalence x1 x2 _) = nub (getVars x1 ++ getVars x2)
getVars (Predication t) = [t]
getVars (ForAll _ x _) = getVars x
getVars (Exists _ x _) = getVars x
getVars _ = []

uniqueQuantifiedVars :: Int -> String -> FORMULA -> (Int, FORMULA)
uniqueQuantifiedVars c = uniqueQuantifiedVars' c Map.empty

uniqueQuantifiedVars' :: Int -> Map.Map Token Token
  -> String -> FORMULA -> (Int, FORMULA)
uniqueQuantifiedVars' c m p f = let u = uniqueQuantifiedVars' c m p in
  case f of
    (Negation x n) -> let (c1, x1) = u x in (c1, Negation x1 n)
    (Conjunction fs n) -> let
        (c1, fs1) = foldr (\ x (cx1, xs) -> let
          (cx2, fx) = uniqueQuantifiedVars' cx1 m p x in (cx2, fx : xs))
          (0, []) fs
      in (c1, Conjunction fs1 n)
    (Disjunction fs n) -> let
        (c1, fs1) = foldr (\ x (cx1, xs) -> let
          (cx2, fx) = uniqueQuantifiedVars' cx1 m p x in (cx2, fx : xs))
          (0, []) fs
      in (c1, Disjunction fs1 n)
    (Implication x1 x2 n) -> let
        (c1, x1') = u x1
        (c2, x2') = uniqueQuantifiedVars' c1 m p x2
      in (c2, Implication x1' x2' n)
    (Equivalence x1 x2 n) -> let
        (c1, x1') = u x1
        (c2, x2') = uniqueQuantifiedVars' c1 m p x2
      in (c2, Equivalence x1' x2' n)
    a@(TrueAtom _) -> (c, a)
    a@(FalseAtom _) -> (c, a)
    (Predication t) -> case Map.lookup t m of
                         Nothing -> (c, Predication t)
                         Just t1 -> (c, Predication t1)
    (ForAll ts x n) -> let
        c1 = c + length ts
        (m1, ts1) = foldr (\ i (m', ts') ->
          (Map.insert (ts !! (i - c)) (Token (p ++ show i) nullRange) m',
            Token (p ++ show i) nullRange : ts')) (m, []) [c .. (c1 - 1)]
        (c2, x') = uniqueQuantifiedVars' c1 m1 p x
      in
        (c2, ForAll ts1 x' n)
    (Exists ts x n) -> let
        c1 = c + length ts
        (m1, ts1) = foldr (\ i (m', ts') ->
          (Map.insert (ts !! (i - c)) (Token (p ++ show i) nullRange) m',
            Token (p ++ show i) nullRange : ts')) (m, []) [c .. (c1 - 1)]
        (c2, x') = uniqueQuantifiedVars' c1 m1 p x
      in
        (c2, Exists ts1 x' n)

removeQuantifiers :: FORMULA -> FORMULA
removeQuantifiers = foldFormula mapRecord
  { foldForAll = \ _ x _ -> x
  , foldExists = \ _ x _ -> x }

data QuantifiedVars = QuantifiedVars
  { universallyQ :: [Token]
  , existentiallyQ :: [Token]
  , notQ :: [Token] } deriving (Show)

quantifiedVars :: QuantifiedVars
quantifiedVars = QuantifiedVars
  { universallyQ = []
  , existentiallyQ = []
  , notQ = [] }

joinQuantifiedVars :: QuantifiedVars -> QuantifiedVars -> QuantifiedVars
joinQuantifiedVars q1 q2 = let
    u = nub (universallyQ q1 ++ universallyQ q2)
    e = nub (existentiallyQ q1 ++ existentiallyQ q2) \\ u
    n = nub (notQ q1 ++ notQ q2) \\ (u ++ e) {- if all formulas have been
    sanitized properly (NotQ q1) \\ (u++e) == (NotQ q1) and
    (NotQ q2) \\ (u++e) == (NotQ q2) should hold -
    see ProverState.hs - showQDIMACSProblem for an example on how
    to use uniqueQuantifiedVars to achieve that -}
  in
    QuantifiedVars
    { universallyQ = u
    , existentiallyQ = e
    , notQ = n }

getQuantifiedVars :: FORMULA -> QuantifiedVars
getQuantifiedVars f = case f of
  (Negation x _) -> getQuantifiedVars x
  (Conjunction xs _) -> foldr joinQuantifiedVars quantifiedVars
    (map getQuantifiedVars xs)
  (Disjunction xs _) -> foldr joinQuantifiedVars quantifiedVars
    (map getQuantifiedVars xs)
  (Implication x1 x2 _) -> joinQuantifiedVars (getQuantifiedVars x1)
    (getQuantifiedVars x2)
  (Equivalence x1 x2 _) -> joinQuantifiedVars (getQuantifiedVars x1)
    (getQuantifiedVars x2)
  (Predication t) -> quantifiedVars { notQ = [t] }
  (ForAll ts x _) -> joinQuantifiedVars
    (quantifiedVars { universallyQ = ts }) (getQuantifiedVars x)
  (Exists ts x _) -> joinQuantifiedVars
    (quantifiedVars { existentiallyQ = ts }) (getQuantifiedVars x)
  _ -> quantifiedVars

-- | the flatten functions use associtivity to "flatten" the syntax
-- | tree of the formulae

-- | flatten \"flattens\" formulae under the assumption of the
-- | semantics of basic specs, this means that we put each
-- | \"clause\" into a single formula for CNF we really will obtain
-- | clauses

flatten :: FORMULA -> [FORMULA]
flatten f = case f of
      Conjunction fs _ -> concatMap flatten fs
      _ -> [f]

-- | "flattening" for disjunctions
flattenDis :: FORMULA -> [FORMULA]
flattenDis f = case f of
      Disjunction fs _ -> concatMap flattenDis fs
      _ -> [f]

-- | negate a formula
negateFormula :: FORMULA -> FORMULA
negateFormula f = case f of
  FalseAtom ps -> TrueAtom ps
  TrueAtom ps -> FalseAtom ps
  Negation nf _ -> nf
  _ -> Negation f nullRange
