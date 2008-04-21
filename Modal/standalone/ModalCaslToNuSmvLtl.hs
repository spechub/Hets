{-# OPTIONS -fglasgow-exts #-}

module ModalCaslToNuSmvLtl where

import Data.Maybe as Maybe
import Control.Monad as Monad

import NuSmvLtl as Ltl
import ModalCasl as Casl



{------------------------------------------------------------------------------}
{-                                                                            -}
{-  Convert Modal CASL formulas to LTL formulas recognized by NuSMV           -}
{-                                                                            -}
{------------------------------------------------------------------------------}


convert :: Casl.StateFormula a -> Maybe (Ltl.Formula a)

convert (Casl.Var x) =  Just (Ltl.Var x)
convert (Casl.A phi) =  convert' phi
convert _            =  Nothing


convert' :: Casl.PathFormula a -> Maybe (Ltl.Formula a)

convert' (Casl.State  (Casl.Var x)) =  Just (Ltl.Var x)

convert' (Casl.Pnot   phi)          =  liftM  Ltl.Not (convert' phi)
convert' (Casl.Pand   phi psi)      =  liftM2 Ltl.And (convert' phi) (convert' psi)
convert' (Casl.Por    phi psi)      =  liftM2 Ltl.Or  (convert' phi) (convert' psi)

convert' (Casl.X      phi)          =  liftM  Ltl.X   (convert' phi)
convert' (Casl.G      phi)          =  liftM  Ltl.G   (convert' phi)
convert' (Casl.F      phi)          =  liftM  Ltl.F   (convert' phi)

convert' (Casl.W      phi psi)      =  convert'       (Casl.B (Casl.Pand phi psi) (Casl.Pand (Casl.Pnot phi) psi))
convert' (Casl.U      phi psi)      =  convert'       (Casl.B psi (Casl.Pand (Casl.Pnot phi) (Casl.Pnot psi)))
convert' (Casl.B      phi psi)      =  liftM2 Ltl.V   (convert' phi) (convert' psi)

convert' (Casl.W'     phi psi)      =  convert'       (Casl.U' (Casl.Pnot psi) (Casl.Pand phi psi))
convert' (Casl.U'     phi psi)      =  liftM2 Ltl.U   (convert' phi) (convert' psi)
convert' (Casl.B'     phi psi)      =  convert'       (Casl.U' (Casl.Pnot psi) (Casl.Pand phi (Casl.Pnot psi)))

convert' (Casl.XPast  phi)          =  liftM  Ltl.Y   (convert' phi)
convert' (Casl.GPast  phi)          =  liftM  Ltl.H   (convert' phi)
convert' (Casl.FPast  phi)          =  liftM  Ltl.O   (convert' phi)

convert' (Casl.WPast  phi psi)      =  convert'       (Casl.BPast (Casl.Pand phi psi) (Casl.Pand (Casl.Pnot phi) psi))
convert' (Casl.UPast  phi psi)      =  convert'       (Casl.BPast psi (Casl.Pand (Casl.Pnot phi) (Casl.Pnot psi)))
convert' (Casl.BPast  phi psi)      =  liftM2 Ltl.T   (convert' phi) (convert' psi)

convert' (Casl.WPast' phi psi)      =  convert'       (UPast' (Casl.Pnot psi) (Casl.Pand phi psi))
convert' (Casl.UPast' phi psi)      =  liftM2 Ltl.S   (convert' phi) (convert' psi)
convert' (Casl.BPast' phi psi)      =  convert'       (UPast' (Casl.Pnot psi) (Casl.Pand phi (Casl.Pnot psi)))

convert' (Casl.XPast' phi)          =  liftM  Ltl.Z   (convert' phi)

convert' _                          =  Nothing


{------------------------------------------------------------------------------}
