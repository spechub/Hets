{- |
Module      :  $Header$
Copyright   :  (c) Klaus Hartke, Uni Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

-}

module ModalCaslToCtl where

import Control.Monad as Monad
import Data.Maybe as Maybe

import ModalCasl as Casl
import Ctl as Ctl



{------------------------------------------------------------------------------}
{-                                                                            -}
{-  Convert Modal CASL formulas to CTL formulas                               -}
{-                                                                            -}
{------------------------------------------------------------------------------}


convert :: Casl.StateFormula a -> Maybe (Ctl.Formula a)

convert (Casl.Var x)               =  Just (Ctl.Atom x)

convert (Casl.Snot       phi)      =  liftM  Ctl.Not (convert phi)
convert (Casl.Sand       phi psi)  =  liftM2 Ctl.And (convert phi) (convert psi)
convert (Casl.Sor        phi psi)  =  liftM2 Ctl.Or  (convert phi) (convert psi)

convert (Casl.A (Casl.X  phi))     =  liftM  Ctl.AX  (convert' phi)
convert (Casl.E (Casl.X  phi))     =  liftM  Ctl.EX  (convert' phi)
convert (Casl.A (Casl.G  phi))     =  liftM  Ctl.AG  (convert' phi)
convert (Casl.E (Casl.G  phi))     =  liftM  Ctl.EG  (convert' phi)
convert (Casl.A (Casl.F  phi))     =  liftM  Ctl.AF  (convert' phi)
convert (Casl.E (Casl.F  phi))     =  liftM  Ctl.EF  (convert' phi)

convert (Casl.A (Casl.W  phi psi)) =  convert        (Casl.A ((phi `Casl.Pand` psi) `Casl.B` ((Casl.Pnot phi) `Casl.Pand` psi)))
convert (Casl.E (Casl.W  phi psi)) =  convert        (Casl.E ((phi `Casl.Pand` psi) `Casl.B` ((Casl.Pnot phi) `Casl.Pand` psi)))
convert (Casl.A (Casl.U  phi psi)) =  convert        (Casl.A (psi `Casl.Pand` ((Casl.Pnot phi) `Casl.Pand` (Casl.Pnot psi))))
convert (Casl.E (Casl.U  phi psi)) =  convert        (Casl.E (psi `Casl.Pand` ((Casl.Pnot phi) `Casl.Pand` (Casl.Pnot psi))))
convert (Casl.A (Casl.B  phi psi)) =  convert        (Casl.A (Casl.Pnot ((Casl.Pnot phi) `Casl.U'` psi)))
convert (Casl.E (Casl.B  phi psi)) =  convert        (Casl.E (Casl.Pnot ((Casl.Pnot phi) `Casl.U'` psi)))

convert (Casl.A (Casl.W' phi psi)) =  convert        (Casl.A ((Casl.Pnot phi) `Casl.U'` (Casl.Pand phi psi)))
convert (Casl.E (Casl.W' phi psi)) =  convert        (Casl.E ((Casl.Pnot phi) `Casl.U'` (Casl.Pand phi psi)))
convert (Casl.A (Casl.U' phi psi)) =  liftM2 Ctl.AU  (convert' phi) (convert' psi)
convert (Casl.E (Casl.U' phi psi)) =  liftM2 Ctl.EU  (convert' phi) (convert' psi)
convert (Casl.A (Casl.B' phi psi)) =  convert        (Casl.A ((Casl.Pnot phi) `Casl.U'` (Casl.Pand phi (Casl.Pnot psi))))
convert (Casl.E (Casl.B' phi psi)) =  convert        (Casl.E ((Casl.Pnot phi) `Casl.U'` (Casl.Pand phi (Casl.Pnot psi))))

convert _                          =  Nothing


convert' :: Casl.PathFormula a -> Maybe (Ctl.Formula a)

convert' (State     phi)     =  convert phi

convert' (Casl.Pnot phi)     =  liftM  Ctl.Not (convert' phi)
convert' (Casl.Pand phi psi) =  liftM2 Ctl.And (convert' phi) (convert' psi)
convert' (Casl.Por  phi psi) =  liftM2 Ctl.Or  (convert' phi) (convert' psi)

convert' _                   =  Nothing


{------------------------------------------------------------------------------}
