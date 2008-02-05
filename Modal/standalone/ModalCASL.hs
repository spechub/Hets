{-# OPTIONS -fglasgow-exts #-}

module ModalCASL where

import Control.Monad as Monad
import Data.Maybe as Maybe
import Data.Map as Map
import Data.Set as Set

--------------------------------------------------------------------------------
--  Formulas                                                                  --
--------------------------------------------------------------------------------

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
                   --
                   | U'     (PathFormula a) (PathFormula a)
                   | B      (PathFormula a) (PathFormula a)
                   | XPast' (PathFormula a)
                   | XPast  (PathFormula a)
                   | UPast' (PathFormula a) (PathFormula a)
                   | BPast  (PathFormula a) (PathFormula a)
                   | G      (PathFormula a)
                   | GPast  (PathFormula a)
                   | F      (PathFormula a)
                   | FPast  (PathFormula a)
                   | W      (PathFormula a) (PathFormula a)
                   | WPast  (PathFormula a) (PathFormula a)
                   | W'     (PathFormula a) (PathFormula a)
                   | WPast' (PathFormula a) (PathFormula a)
                   | U      (PathFormula a) (PathFormula a)
                   | UPast  (PathFormula a) (PathFormula a)
                   | B'     (PathFormula a) (PathFormula a)
                   | BPast' (PathFormula a) (PathFormula a)
                    deriving (Show)
--------------------------------------------------------------------------------
--  Negation Normal Form                                                      --
--------------------------------------------------------------------------------

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
nnfS (Snot (Mu x        phi    )) =  Nu x        (nnfS (error "Fail"))
nnfS (Snot (Nu x        phi    )) =  Mu x        (nnfS (error "Fail"))

nnfS (Var x              ) =  Var x
nnfS (Sand        phi psi) =  Sand        (nnfS phi) (nnfS psi)
nnfS (Sor         phi psi) =  Sor         (nnfS phi) (nnfS psi)
nnfS (A           phi    ) =  A           (nnfP phi)
nnfS (E           phi    ) =  E           (nnfP phi)
nnfS (Box         phi    ) =  Box         (nnfS phi)
nnfS (Diamond     phi    ) =  Diamond     (nnfS phi)
nnfS (BoxPast     phi    ) =  BoxPast     (nnfS phi)
nnfS (DiamondPast phi    ) =  DiamondPast (nnfS phi)
nnfS (Mu x        phi    ) =  Mu x        (nnfS (error "Fail"))
nnfS (Nu x        phi    ) =  Nu x        (nnfS (error "Fail"))

nnfP :: PathFormula a -> PathFormula a

nnfP (Pnot (Pnot   phi    )) =  nnfP phi
nnfP (Pnot (Pand   phi psi)) =  Por    (nnfP (Pnot phi)) (nnfP (Pnot psi))
nnfP (Pnot (Por    phi psi)) =  Pand   (nnfP (Pnot phi)) (nnfP (Pnot psi))
nnfP (Pnot (X      phi    )) =  X      (nnfP (Pnot phi))
nnfP (Pnot (G      phi    )) =  F      (nnfP (Pnot phi))
nnfP (Pnot (F      phi    )) =  G      (nnfP (Pnot phi))
nnfP (Pnot (W      phi psi)) =  W'     (nnfP (Pnot phi)) (nnfP psi)
nnfP (Pnot (W'     phi psi)) =  W      (nnfP (Pnot phi)) (nnfP psi)
nnfP (Pnot (U      phi psi)) =  B'     (nnfP (Pnot phi)) (nnfP psi)
nnfP (Pnot (U'     phi psi)) =  B      (nnfP (Pnot phi)) (nnfP psi)
nnfP (Pnot (B      phi psi)) =  U'     (nnfP (Pnot phi)) (nnfP psi)
nnfP (Pnot (B'     phi psi)) =  U      (nnfP (Pnot phi)) (nnfP psi)
nnfP (Pnot (XPast  phi    )) =  XPast' (nnfP (Pnot phi))
nnfP (Pnot (XPast' phi    )) =  XPast  (nnfP (Pnot phi))
nnfP (Pnot (GPast  phi    )) =  FPast  (nnfP (Pnot phi))
nnfP (Pnot (FPast  phi    )) =  GPast  (nnfP (Pnot phi))
nnfP (Pnot (WPast  phi psi)) =  WPast' (nnfP (Pnot phi)) (nnfP psi)
nnfP (Pnot (WPast' phi psi)) =  WPast  (nnfP (Pnot phi)) (nnfP psi)
nnfP (Pnot (UPast  phi psi)) =  BPast' (nnfP (Pnot phi)) (nnfP psi)
nnfP (Pnot (UPast' phi psi)) =  BPast  (nnfP (Pnot phi)) (nnfP psi)
nnfP (Pnot (BPast  phi psi)) =  UPast' (nnfP (Pnot phi)) (nnfP psi)
nnfP (Pnot (BPast' phi psi)) =  UPast  (nnfP (Pnot phi)) (nnfP psi)
nnfP (Pnot (SF     phi    )) =  SF     (nnfS (Snot phi))

nnfP (Pand   phi psi) =  Pand   (nnfP phi) (nnfP psi)
nnfP (Por    phi psi) =  Por    (nnfP phi) (nnfP psi)
nnfP (X      phi    ) =  X      (nnfP phi)
nnfP (G      phi    ) =  G      (nnfP phi)
nnfP (F      phi    ) =  F      (nnfP phi)
nnfP (W      phi psi) =  W      (nnfP phi) (nnfP psi)
nnfP (W'     phi psi) =  W'     (nnfP phi) (nnfP psi)
nnfP (U      phi psi) =  U      (nnfP phi) (nnfP psi)
nnfP (U'     phi psi) =  U'     (nnfP phi) (nnfP psi)
nnfP (B      phi psi) =  B      (nnfP phi) (nnfP psi)
nnfP (B'     phi psi) =  B'     (nnfP phi) (nnfP psi)
nnfP (XPast  phi    ) =  XPast  (nnfP phi) 
nnfP (XPast' phi    ) =  XPast' (nnfP phi) 
nnfP (GPast  phi    ) =  GPast  (nnfP phi) 
nnfP (FPast  phi    ) =  FPast  (nnfP phi) 
nnfP (WPast  phi psi) =  WPast  (nnfP phi) (nnfP psi)
nnfP (WPast' phi psi) =  WPast' (nnfP phi) (nnfP psi)
nnfP (UPast  phi psi) =  UPast  (nnfP phi) (nnfP psi)
nnfP (UPast' phi psi) =  UPast' (nnfP phi) (nnfP psi)
nnfP (BPast  phi psi) =  BPast  (nnfP phi) (nnfP psi)
nnfP (BPast' phi psi) =  BPast' (nnfP phi) (nnfP psi)
nnfP (SF     phi    ) =  SF     (nnfS phi) 

--------------------------------------------------------------------------------
--  µ Normal Form                                                             --
--------------------------------------------------------------------------------

munf :: StateFormula a -> StateFormula a

munf phi = munf' (nnfS phi)
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
        munf' (E (SF phi))       =  Sand (munf' phi) phiinf where phiinf = error "???"
        munf' (E (Por phi psi))  =  Sor (munf' (E phi)) (munf' (E psi))
        munf' (E (X phi))        =  Sand (Diamond (munf' (E phi))) phiinf where phiinf = error "???" --nu x.diamond x
        munf' (E (Pand phi psi)) =  error "Read the fucking book, pg. 100"


--------------------------------------------------------------------------------
--  CTL to µ-Calculus                                                         --
--------------------------------------------------------------------------------

--cmu :: StateFormula a -> StateFormula a


--------------------------------------------------------------------------------
--  CTL² to CTL                                                               --
--------------------------------------------------------------------------------

c2c :: StateFormula a -> StateFormula a

c2c (E (X  (X  (SF a))))               =  E (X (SF (E (X  (SF a)))))
c2c (E (X  (U' (SF a) (SF b))))        =  E (X (SF (E (U' (SF a) (SF b)))))
c2c (E (X  (B  (SF a) (SF b))))        =  E (X (SF (E (B  (SF a) (SF b)))))
c2c (E (U' (X  (SF a)) (SF b)))        =  Sor b (E (X (SF (E (U' (SF a) (Pand (SF a) (SF b)))))))
c2c (E (U' (U' (SF a) (SF b)) (SF c))) =  c `Sor` (E ((SF (a `Sor` b)) `U'` (SF (b `Sand` (E (X (SF c))) `Sor` c `Sand` E ((SF a) `U'` (SF b))))))
c2c (E (U' (B  (SF a) (SF b)) (SF c))) =  c `Sor` (E ((Pnot (SF b)) `U'` (SF (a `Sand` Snot b `Sand` E (X (SF c)) `Sor` c `Sand` E ((SF a) `B` (SF b))))))
c2c (E (U' (SF a) (X (SF b))))         =  E ((SF a) `U'` (SF (E (X (SF b)))))
c2c (E (U' (SF a) (U' (SF b) (SF c)))) =  E ((SF a) `U'` (SF (E ((SF b) `U'` (SF c)))))
c2c (E (U' (SF a) (B  (SF b) (SF c)))) =  E ((SF a) `U'` (SF (E ((SF b) `B`  (SF c)))))
c2c (E (B  (X  (SF a)) (SF b)))        =  E (SF (E (X (SF a))) `B` (SF b))
c2c (E (B  (U' (SF a) (SF b)) (SF c))) =  E ((SF (E ((SF a) `B` (SF b)))) `U'` (SF c))
c2c (E (B  (B  (SF a) (SF b)) (SF c))) =  E ((SF (E ((SF a) `B` (SF b)))) `B`  (SF c))
--c2c (E 

--------------------------------------------------------------------------------
--  Class                                                                     --
--------------------------------------------------------------------------------

class Kripke k a s | k -> a s where
    states  :: k -> Set s
    initial :: k -> Set s
    next    :: k -> s -> Set s
    labels  :: k -> s -> Set a

{-


-- BooelanFormula: see logic Bool in Hets

class BooleanSymbolicKripke k id a | k -> a where
    vars :: k -> Set id
    initialBoolSym :: k -> BooleanFormula id
    nextBoolSym :: k -> BooleanFormula id
    labelsBoolSym :: k -> a -> BooleanFormula id

-- states = Boolean valuations, represented as sets of ids
-- set of initial states and transitions are predicates, expressed as Boolean formulas    
class BooleanSymbolicKripke k id a => class Kripe k a (Set id) where
    next k s = "set of all states s' such that nextBoolSym k is true in the valuation (s,s')"    
      -- s is valuation of the variables in vars k
      -- s' is valuation of primed variants of those variables


-}

--------------------------------------------------------------------------------
--  Renaming                                                                  --
--------------------------------------------------------------------------------

alphaint :: (Ord a) => StateFormula a -> StateFormula Int
alphaint = alpha (+1) 1

alpha :: (Ord a) => (b -> b) -> b -> StateFormula a -> StateFormula b
alpha f n = fst . alphaS Map.empty n
    where
        alphaS m n (Var x              ) =  (Var (Maybe.fromJust (Map.lookup x m)), n)
        alphaS m n (Snot        phi    ) =  (Snot        phi'     , n' ) where (phi', n' ) =  alphaS m                  n     phi
        alphaS m n (Sand        phi psi) =  (Sand        phi' psi', n'') where (phi', n' ) =  alphaS m                  n     phi
                                                                               (psi', n'') =  alphaS m                  n'    psi
        alphaS m n (Sor         phi psi) =  (Sor         phi' psi', n'') where (phi', n' ) =  alphaS m                  n     phi
                                                                               (psi', n'') =  alphaS m                  n'    psi
        alphaS m n (E           phi    ) =  (E           phi'     , n' ) where (phi', n' ) =  alphaP m                  n     phi
        alphaS m n (A           phi    ) =  (A           phi'     , n' ) where (phi', n' ) =  alphaP m                  n     phi
        alphaS m n (Diamond     phi    ) =  (Diamond     phi'     , n' ) where (phi', n' ) =  alphaS m                  n     phi
        alphaS m n (Box         phi    ) =  (Box         phi'     , n' ) where (phi', n' ) =  alphaS m                  n     phi
        alphaS m n (DiamondPast phi    ) =  (DiamondPast phi'     , n' ) where (phi', n' ) =  alphaS m                  n     phi
        alphaS m n (BoxPast     phi    ) =  (BoxPast     phi'     , n' ) where (phi', n' ) =  alphaS m                  n     phi
        alphaS m n (Mu x        phi    ) =  (Mu n        phi'     , n'') where (phi', n'') =  alphaS (Map.insert x n m) (f n) phi
        alphaS m n (Nu x        phi    ) =  (Nu n        phi'     , n'') where (phi', n'') =  alphaS (Map.insert x n m) (f n) phi
        
        alphaP m n (SF     phi    ) =  (SF     phi'     , n' ) where (phi', n' ) = alphaS m n phi
        alphaP m n (Pnot   phi    ) =  (Pnot   phi'     , n' ) where (phi', n' ) = alphaP m n phi
        alphaP m n (Pand   phi psi) =  (Pand   phi' psi', n'') where (phi', n' ) = alphaP m n phi
                                                                     (psi', n'') = alphaP m n psi
        alphaP m n (Por    phi psi) =  (Por    phi' psi', n'') where (phi', n' ) = alphaP m n phi
                                                                     (psi', n'') = alphaP m n psi
        alphaP m n (X      phi    ) =  (X      phi'     , n' ) where (phi', n' ) = alphaP m n phi


--------------------------------------------------------------------------------
--  Local Model Checker                                                       --
--------------------------------------------------------------------------------

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


sucE :: (Kripke m a s, Ord a, Ord s) =>  m -> Set s -> Set s
sucE k y =  Set.fold (Set.union . next k) Set.empty y

preE :: (Kripke m a s, Ord a, Ord s) =>  m -> Set s -> Set s
preE k y =  Set.filter (not . Set.null . Set.intersection y . next k) (states k)


localCheck :: (Kripke k a s, Ord a, Ord s, Ord (s, StateFormula a)) => (k, s) -> StateFormula a -> Bool
localCheck (k, s) phi = localCheck' s phi' Set.empty
    where
        phi' = nnfS phi
        
        localCheck' s (Snot        phi    ) callStack =  not $ Set.member x (labels k s) where Var x = phi
        localCheck' s (Sand        phi psi) callStack =  conj2 callStack $ Set.fromList [ (s, phi), (s, psi) ]
        localCheck' s (Sor         phi psi) callStack =  disj2 callStack $ Set.fromList [ (s, phi), (s, psi) ]
        localCheck' s (Mu x        phi    ) callStack =  localCheck' s phi $ Set.insert (s, Mu x phi) callStack
        localCheck' s (Nu x        phi    ) callStack =  localCheck' s phi $ Set.insert (s, Nu x phi) callStack
	localCheck' s (Diamond     phi    ) callStack =  disj2 callStack $ Set.map (flip (,) phi) $ sucE k (Set.singleton s)
	localCheck' s (Box         phi    ) callStack =  conj2 callStack $ Set.map (flip (,) phi) $ sucE k (Set.singleton s)
	localCheck' s (DiamondPast phi    ) callStack =  disj2 callStack $ Set.map (flip (,) phi) $ preE k (Set.singleton s)
	localCheck' s (BoxPast     phi    ) callStack =  conj2 callStack $ Set.map (flip (,) phi) $ preE k (Set.singleton s)
	localCheck' s (Var x              ) callStack =  case d phi' x of
	                                                     Nothing -> Set.member x (labels k s)
	                                                     Just d' -> if Set.member (s, d') callStack then
	                                                                    case d' of
	                                                                        Mu _ _ -> True
	                                                                        Nu _ _ -> False
	                                                                else
	                                                                    localCheck' s d' callStack
        
        disj2 callStack =  flip Set.fold True  $ \(s, phi) b -> b && localCheck' s phi callStack
        
        conj2 callStack =  flip Set.fold False $ \(s, phi) b -> b || localCheck' s phi callStack

--------------------------------------------------------------------------------


