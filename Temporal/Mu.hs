{-# OPTIONS -fglasgow-exts #-}

module Mu where

import Control.Monad as Monad
import Data.Set as Set
import Kripke



{------------------------------------------------------------------------------}
{-                                                                            -}
{-  Formulas of the µ-Calculus                                                -}
{-                                                                            -}
{------------------------------------------------------------------------------}

--
-- Given a finite set of variables, the set of µ-calculus pre-formulas is the
-- set of formulas that can be derived from the following definitions:
--

data StateFormula a = Var a
                    | Snot        (StateFormula a)
                    | Sand        (StateFormula a) (StateFormula a)
                    | Sor         (StateFormula a) (StateFormula a)
                    | E           (PathFormula a)
                    | A           (PathFormula a)
                    | Diamond     (StateFormula a)
                    | Box         (StateFormula a)
                    | DiamondPast (StateFormula a)
                    | BoxPast     (StateFormula a)
                    | Mu a        (StateFormula a)
                    | Nu a        (StateFormula a)
                     deriving (Show)


data PathFormula a = SF     (StateFormula a)
                   | Pnot   (PathFormula a)
                   | Pand   (PathFormula a) (PathFormula a)
                   | Por    (PathFormula a) (PathFormula a)
                   | X      (PathFormula a)
                    deriving (Show)

--
-- The set of µ-calculus formulas is the subset of pre-formulas where each
-- subformula of the form (Mu x phi) or (Nu x phi) statisfies the constraint
-- that all occurrences of x in phi occur under an even number of negation
-- symbols.
--
-- A subformula, where all X operators occur in the scope of a path quantifier
-- (E or A) is a state formula, otherwise it is a path formula. The semantics
-- of state formulas is defined on states, while the semantics of path formulas
-- is defined on paths of the Kripke structure.
--



{------------------------------------------------------------------------------}
{-                                                                            -}
{-  Negation Normal Form                                                      -}
{-                                                                            -}
{------------------------------------------------------------------------------}

nnfS :: StateFormula a -> StateFormula a

nnfS (Snot (Var x              )) =  Snot (Var x)
nnfS (Snot (Snot        phi    )) =  nnfS phi
nnfS (Snot (Sand        phi psi)) =  Sor         (nnfS (Snot phi)) (nnfS (Snot psi))
nnfS (Snot (Sor         phi psi)) =  Sand        (nnfS (Snot phi)) (nnfS (Snot psi))
nnfS (Snot (A           phi    )) =  E           (nnfP (Pnot phi))
nnfS (Snot (E           phi    )) =  A           (nnfP (Pnot phi))
nnfS (Snot (Box         phi    )) =  Diamond     (nnfS (Snot phi))
nnfS (Snot (Diamond     phi    )) =  Box         (nnfS (Snot phi))
nnfS (Snot (BoxPast     phi    )) =  DiamondPast (nnfS (Snot phi))
nnfS (Snot (DiamondPast phi    )) =  BoxPast     (nnfS (Snot phi))
nnfS (Snot (Mu x        phi    )) =  Nu x        (nnfS (Snot phi))
nnfS (Snot (Nu x        phi    )) =  Mu x        (nnfS (Snot phi))

nnfS (Var x              ) =  Var x
nnfS (Sand        phi psi) =  Sand        (nnfS phi) (nnfS psi)
nnfS (Sor         phi psi) =  Sor         (nnfS phi) (nnfS psi)
nnfS (A           phi    ) =  A           (nnfP phi)
nnfS (E           phi    ) =  E           (nnfP phi)
nnfS (Box         phi    ) =  Box         (nnfS phi)
nnfS (Diamond     phi    ) =  Diamond     (nnfS phi)
nnfS (BoxPast     phi    ) =  BoxPast     (nnfS phi)
nnfS (DiamondPast phi    ) =  DiamondPast (nnfS phi)
nnfS (Mu x        phi    ) =  Mu x        (nnfS phi)
nnfS (Nu x        phi    ) =  Nu x        (nnfS phi)


nnfP :: PathFormula a -> PathFormula a

nnfP (Pnot (Pnot   phi    )) =  nnfP phi
nnfP (Pnot (Pand   phi psi)) =  Por  (nnfP (Pnot phi)) (nnfP (Pnot psi))
nnfP (Pnot (Por    phi psi)) =  Pand (nnfP (Pnot phi)) (nnfP (Pnot psi))
nnfP (Pnot (X      phi    )) =  X    (nnfP (Pnot phi))
nnfP (Pnot (SF     phi    )) =  SF   (nnfS (Snot phi))

nnfP (Pand   phi psi) =  Pand (nnfP phi) (nnfP psi)
nnfP (Por    phi psi) =  Por  (nnfP phi) (nnfP psi)
nnfP (X      phi    ) =  X    (nnfP phi)
nnfP (SF     phi    ) =  SF   (nnfS phi)



{------------------------------------------------------------------------------}
{-                                                                            -}
{-  Normal Form of µ-Calculus Formulas                                        -}
{-                                                                            -}
{------------------------------------------------------------------------------}

--
-- For every formula of the µ-calculus, there is an equivalent formula of the
-- µ-calculus where neither path quantifiers E, A nor X operators occur.
--
-- We ensure that the given formula is in negation normal form. Hence, negation
-- symbols only occur in front of variables, which means that we can neglect
-- Pnot.
--

munf :: Set a -> StateFormula a -> StateFormula a

munf vars phi = munf' (nnfS phi)
    where
        munf' (Var x)            =  Var x
        munf' (Snot (Var x))     =  Snot (Var x)
        munf' (Sand phi psi)     =  Sand (munf' phi) (munf' psi)
        munf' (Sor phi psi)      =  Sor (munf' phi) (munf' psi)
        munf' (Mu x phi)         =  Mu x (munf' phi)
        munf' (Nu x phi)         =  Nu x (munf' phi)
        munf' (Diamond phi)      =  Diamond (munf' phi)
        munf' (Box phi)          =  Box (munf' phi)
        munf' (DiamondPast phi)  =  DiamondPast (munf' phi)
        munf' (BoxPast phi)      =  BoxPast (munf' phi)
        munf' (A phi)            =  Snot (munf' (E (nnfP (Pnot phi))))
        munf' (E (SF phi))       =  Sand (munf' phi) phiinf 
        munf' (E (Por phi psi))  =  Sor (munf' (E phi)) (munf' (E psi))
        munf' (E (X phi))        =  Sand (Diamond (munf' (E phi))) phiinf
        munf' (E (Pand phi psi)) =  error "Read the fucking book, pg. 100"
        
        phiinf = Nu (Set.findMin vars) (Diamond (Var (Set.findMin vars)))



{------------------------------------------------------------------------------}
{-                                                                            -}
{-  Local Model Checking for the µ-Calculus                                   -}
{-                                                                            -}
{------------------------------------------------------------------------------}

-- 
-- We assume that the considered formulas fulfill the following syntactic
-- requirements, that can be achieved without loss of generality:
-- 
--   * We only consider formulas in guarded normal form, so that every bound
--     variable occurs in the scope of a modal operator. Moreover, we assume
--     negation normal form, so that negation symbols only occur before
--     variables (that are not bound).
-- 
--   * We assume that every bound variable is bound only once and has no free
--     occurrences, so that we can define for a formula an associated function
--     that maps a bound variable to the unique subformula where the variable
--     is bound.
-- 

d :: (Eq a) => StateFormula a -> a -> Maybe (StateFormula a)

d (Snot phi)        x =  d phi x
d (Sand phi psi)    x =  Monad.mplus (d phi x) (d psi x)
d (Sor phi psi)     x =  Monad.mplus (d phi x) (d psi x)
d (Mu x' phi)       x =  if x' == x then Just (Mu x' phi) else d phi x
d (Nu x' phi)       x =  if x' == x then Just (Nu x' phi) else d phi x
d (Diamond phi)     x =  d phi x
d (Box phi)         x =  d phi x
d (DiamondPast phi) x =  d phi x
d (BoxPast phi)     x =  d phi x
d (Var x')          x =  Nothing


sucE :: (Kripke m a s, Ord a, Ord s) => m -> Set s -> Set s

sucE k y =  Set.fold (Set.union . next k) Set.empty y


preE :: (Kripke m a s, Ord a, Ord s) => m -> Set s -> Set s

preE k y =  Set.filter (not . Set.null . Set.intersection y . next k) (states k)


localCheck :: (Kripke k a s, Ord a, Ord s, Ord (s, StateFormula a)) => (k, s) -> StateFormula a -> Bool

localCheck (k, s) phi = localCheck' s phi Set.empty
    where
        localCheck' s (Snot        (Var x)) callStack =  not $ Set.member x (labels k s)
        localCheck' s (Sand        phi psi) callStack =  conj2 callStack $ Set.fromList [ (s, phi), (s, psi) ]
        localCheck' s (Sor         phi psi) callStack =  disj2 callStack $ Set.fromList [ (s, phi), (s, psi) ]
        localCheck' s (Mu x        phi    ) callStack =  localCheck' s phi $ Set.insert (s, Mu x phi) callStack
        localCheck' s (Nu x        phi    ) callStack =  localCheck' s phi $ Set.insert (s, Nu x phi) callStack
        localCheck' s (Diamond     phi    ) callStack =  disj2 callStack $ Set.map (flip (,) phi) $ sucE k (Set.singleton s)
        localCheck' s (Box         phi    ) callStack =  conj2 callStack $ Set.map (flip (,) phi) $ sucE k (Set.singleton s)
        localCheck' s (DiamondPast phi    ) callStack =  disj2 callStack $ Set.map (flip (,) phi) $ preE k (Set.singleton s)
        localCheck' s (BoxPast     phi    ) callStack =  conj2 callStack $ Set.map (flip (,) phi) $ preE k (Set.singleton s)
        localCheck' s (Var x              ) callStack =  case d phi x of
                                                             Nothing -> Set.member x (labels k s)
                                                             Just d' -> if Set.member (s, d') callStack then
                                                                            case d' of
                                                                                Mu _ _ -> True
                                                                                Nu _ _ -> False
                                                                        else
                                                                            localCheck' s d' callStack
        
        disj2 callStack =  flip Set.fold True  $ \(s, phi) b -> b && localCheck' s phi callStack
        
        conj2 callStack =  flip Set.fold False $ \(s, phi) b -> b || localCheck' s phi callStack



{------------------------------------------------------------------------------}
