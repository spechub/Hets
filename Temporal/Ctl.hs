{-# OPTIONS -fglasgow-exts #-}

module Ctl where

import Data.Set as Set

exists :: (a -> Bool) -> Set a -> Bool
exists f = Set.fold ((||) . f) False

infixr 3  `And`
infixr 2  `Or`
infixr 1  `Implies`
infixl 1  `AU`, `EU`
infix  0  |=

-- ctl formulas

data Formula a =
      Top
    | Bottom
    | Atom a
    | Not (Formula a)
    | (Formula a) `And` (Formula a)
    | (Formula a) `Or` (Formula a)
    | (Formula a) `Implies` (Formula a)
    | AX (Formula a)
    | EX (Formula a)
    | AF (Formula a)
    | EF (Formula a)
    | AG (Formula a)
    | EG (Formula a)
    | (Formula a) `AU` (Formula a)
    | (Formula a) `EU` (Formula a)
    deriving Show

-- ctl class

class CTL m a s | m -> a s where
    states :: m -> Set s
    next   :: m -> s -> Set s
    labels :: m -> s -> Set a

-- satisfaction relation

(|=) :: (CTL m a s, Ord a, Ord s) =>  (m, s) -> Formula a -> Bool
(m, s) |= phi =  Set.member s (sat m phi)

sat :: (CTL m a s, Ord a, Ord s) =>  m -> Formula a -> Set s
sat m Top                 =  states m
sat m Bottom              =  Set.empty
sat m (Atom a)            =  Set.filter (Set.member a . labels m) (states m)
sat m (Not phi)           =  Set.difference (states m) (sat m phi)
sat m (phi `And` psi)     =  Set.intersection (sat m phi) (sat m psi)
sat m (phi `Or` psi)      =  Set.union (sat m phi) (sat m psi)
sat m (phi `Implies` psi) =  sat m (Not phi `Or` psi)
sat m (AX phi)            =  sat m (Not (EX (Not phi)))
sat m (EX phi)            =  satEX m phi
sat m (phi `AU` psi)      =  sat m (Not (Not psi `EU` (Not phi `And` Not psi) `Or` EG (Not psi)))
sat m (phi `EU` psi)      =  satEU m phi psi
sat m (EF phi)            =  sat m (Top `EU` phi)
sat m (EG phi)            =  sat m (Not (AF (Not phi)))
sat m (AF phi)            =  satAF m phi
sat m (AG phi)            =  sat m (Not (EF (Not phi)))

satEX :: (CTL m a s, Ord a, Ord s) =>  m -> Formula a -> Set s
satEX m phi =  preE m (sat m phi)

satAF :: (CTL m a s, Ord a, Ord s) =>  m -> Formula a -> Set s
satAF m phi =  satAF' (states m) (sat m phi)
    where
        satAF' x y =  if x == y then y else satAF' y (Set.union y (preA m y))

satEU :: (CTL m a s, Ord a, Ord s) =>  m -> Formula a -> Formula a -> Set s
satEU m phi psi =  satEU' (sat m phi) (states m) (sat m psi)
    where
        satEU' w x y =  if x == y then y else satEU' w y (Set.union y (Set.intersection w (preE m y)))

preE :: (CTL m a s, Ord a, Ord s) =>  m -> Set s -> Set s
preE m y =  Set.filter (\s-> exists (flip Set.member (next m s)) y) (states m)

preA :: (CTL m a s, Ord a, Ord s) =>  m -> Set s -> Set s
preA m y =  Set.difference (states m) (preE m (Set.difference (states m) y))

-- test model

data My       =  My
data MyAtoms  =  P  | Q  | R   deriving (Eq, Ord, Show)
data MyStates =  S0 | S1 | S2  deriving (Eq, Ord, Show)

instance CTL My MyAtoms MyStates where
    states My    =  Set.fromList [S0, S1, S2]
    next   My S0 =  Set.fromList [S1, S2]
    next   My S1 =  Set.fromList [S0, S2]
    next   My S2 =  Set.fromList [S2]
    labels My S0 =  Set.fromList [P, Q]
    labels My S1 =  Set.fromList [Q, R]
    labels My S2 =  Set.fromList [R]
