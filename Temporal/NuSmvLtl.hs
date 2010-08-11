{-# OPTIONS -fglasgow-exts #-}
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

module NuSmvLtl where



{------------------------------------------------------------------------------}
{-                                                                            -}
{-  LTL Specifications                                                        -}
{-                                                                            -}
{------------------------------------------------------------------------------}

--
-- LTL specifications are introduced by the keyword LTLSPEC. The syntax
-- of LTL formulas recognized by NuSMV is as follows:
--

data Formula a =  Var a
               |  Not   (Formula a)                   -- logical not
               |  And   (Formula a) (Formula a)       -- logical and
               |  Or    (Formula a) (Formula a)       -- logical or
               |  Xor   (Formula a) (Formula a)       -- logical exlusive or
               |  Impl  (Formula a) (Formula a)       -- logical implies
               |  Equiv (Formula a) (Formula a)       -- logical equivalence
               -- Future
               |  X     (Formula a)                   -- next state
               |  G     (Formula a)                   -- globally
               |  F     (Formula a)                   -- finally
               |  U     (Formula a) (Formula a)       -- until
               |  V     (Formula a) (Formula a)       -- releases
               -- Past
               |  Y     (Formula a)                   -- previous state
               |  Z     (Formula a)                   -- not previous state not
               |  H     (Formula a)                   -- historically
               |  O     (Formula a)                   -- once
               |  S     (Formula a) (Formula a)       -- since
               |  T     (Formula a) (Formula a)       -- triggered


instance (Show a) => Show (Formula a) where
  show phi =  "LTLSPEC " ++ show' phi True ++ ";" where
    show' (Var x)         outer =  show x
    show' (Not phi)       outer =  "! " ++ show' phi False
    show' (And phi psi)   True  =  show' phi False ++ " & " ++ show' psi False
    show' (Or phi psi)    True  =  show' phi False ++ " | " ++ show' psi False
    show' (Xor phi psi)   True  =  show' phi False ++ " xor " ++ show' psi False
    show' (Impl phi psi)  True  =  show' phi False ++ " -> " ++ show' psi False
    show' (Equiv phi psi) True  =  show' phi False ++ " <-> " ++ show' psi False
    show' (X phi)         outer =  "X " ++ show' phi False
    show' (G phi)         outer =  "G " ++ show' phi False
    show' (F phi)         outer =  "F " ++ show' phi False
    show' (U phi psi)     True  =  show' phi False ++ " U " ++ show' psi False
    show' (V phi psi)     True  =  show' phi False ++ " V " ++ show' psi False
    show' (Y phi)         outer =  "Y " ++ show' phi False
    show' (Z phi)         outer =  "Z " ++ show' phi False
    show' (H phi)         outer =  "H " ++ show' phi False
    show' (O phi)         outer =  "O " ++ show' phi False
    show' (S phi psi)     True  =  show' phi False ++ " S " ++ show' psi False
    show' (T phi psi)     True  =  show' phi False ++ " T " ++ show' psi False
    show' phi             False =  "(" ++ show' phi True ++ ")"


{------------------------------------------------------------------------------}
