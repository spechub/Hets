{- |
Module      :  $Header$
Copyright   :  (c) Klaus Hartke, Uni Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

-}

module ModalCaslToMu where

import Control.Monad as Monad
import Data.Maybe as Maybe

import ModalCasl as Casl
import Mu as Mu



{------------------------------------------------------------------------------}
{-                                                                            -}
{-  Convert Modal CASL formulas to formulas of the µ-Calculus                 -}
{-                                                                            -}
{------------------------------------------------------------------------------}

convert :: Casl.StateFormula a -> Maybe (Mu.StateFormula a)

convert (Casl.Var x)               =  Just   (Mu.Var x)

convert (Casl.Snot        phi)     =  liftM  Mu.Snot        (convert  phi)
convert (Casl.Sand        phi psi) =  liftM2 Mu.Sand        (convert  phi) (convert psi)
convert (Casl.Sor         phi psi) =  liftM2 Mu.Sor         (convert  phi) (convert psi)

convert (Casl.E           phi)     =  liftM  Mu.E           (convert' phi)
convert (Casl.A           phi)     =  liftM  Mu.A           (convert' phi)

convert (Casl.Diamond     phi)     =  liftM  Mu.Diamond     (convert  phi)
convert (Casl.Box         phi)     =  liftM  Mu.Box         (convert  phi)

convert (Casl.DiamondPast phi)     =  liftM  Mu.DiamondPast (convert  phi)
convert (Casl.BoxPast     phi)     =  liftM  Mu.BoxPast     (convert  phi)

convert (Casl.Mu x        phi)     =  liftM  (Mu.Mu x)      (convert  phi)
convert (Casl.Nu x        phi)     =  liftM  (Mu.Nu x)      (convert  phi)


convert' :: Casl.PathFormula a -> Maybe (Mu.PathFormula a)

convert' (Casl.State phi)     =  liftM  Mu.SF   (convert  phi)

convert' (Casl.Pnot  phi)     =  liftM  Mu.Pnot (convert' phi)
convert' (Casl.Pand  phi psi) =  liftM2 Mu.Pand (convert' phi) (convert' psi)
convert' (Casl.Por   phi psi) =  liftM2 Mu.Por  (convert' phi) (convert' psi)

convert' (Casl.X     phi)     =  liftM  Mu.X    (convert' phi)

convert' _                    =  Nothing


{------------------------------------------------------------------------------}
