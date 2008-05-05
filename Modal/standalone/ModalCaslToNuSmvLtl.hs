{-# OPTIONS -fglasgow-exts #-}

module ModalCaslToNuSmvLtl where

import Control.Monad as Monad
import Data.Maybe as Maybe
import Text.ParserCombinators.Parsec hiding (State)

import ModalCasl as Casl
import NuSmvLtl as Ltl



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

convert' (Casl.Por (Casl.Pnot phi) psi) = liftM2 Ltl.Impl (convert' phi) (convert' psi)

convert' (Casl.State  (Casl.Var x)) =  Just (Ltl.Var x)

convert' (Casl.Pnot   phi)          =  liftM  Ltl.Not (convert' phi)
convert' (Casl.Pand   phi psi)      =  liftM2 Ltl.And (convert' phi) (convert' psi)
convert' (Casl.Por    phi psi)      =  liftM2 Ltl.Or  (convert' phi) (convert' psi)

convert' (Casl.X      phi)          =  liftM  Ltl.X   (convert' phi)
convert' (Casl.G      phi)          =  liftM  Ltl.G   (convert' phi)
convert' (Casl.F      phi)          =  liftM  Ltl.F   (convert' phi)

convert' (Casl.W      phi psi)      =  convert'       ((phi `Casl.Pand` psi) `Casl.B` ((Casl.Pnot phi) `Casl.Pand` psi))
convert' (Casl.U      phi psi)      =  convert'       (psi `Casl.B` ((Casl.Pnot phi) `Casl.Pand` (Casl.Pnot psi)))
convert' (Casl.B      phi psi)      =  liftM2 Ltl.V   (convert' phi) (convert' psi)

convert' (Casl.W'     phi psi)      =  convert'       ((Casl.Pnot psi) `Casl.U'` (phi `Casl.Pand` psi))
convert' (Casl.U'     phi psi)      =  liftM2 Ltl.U   (convert' phi) (convert' psi)
convert' (Casl.B'     phi psi)      =  convert'       ((Casl.Pnot psi) `Casl.U'` (phi `Casl.Pand` (Casl.Pnot psi)))

convert' (Casl.XPast  phi)          =  liftM  Ltl.Y   (convert' phi)
convert' (Casl.GPast  phi)          =  liftM  Ltl.H   (convert' phi)
convert' (Casl.FPast  phi)          =  liftM  Ltl.O   (convert' phi)

convert' (Casl.WPast  phi psi)      =  convert'       ((phi `Casl.Pand` psi) `Casl.BPast` ((Casl.Pnot phi) `Casl.Pand` psi))
convert' (Casl.UPast  phi psi)      =  convert'       (psi `Casl.BPast` ((Casl.Pnot phi) `Casl.Pand` (Casl.Pnot psi)))
convert' (Casl.BPast  phi psi)      =  liftM2 Ltl.T   (convert' phi) (convert' psi)

convert' (Casl.WPast' phi psi)      =  convert'       ((Casl.Pnot psi) `Casl.UPast'` (phi `Casl.Pand` psi))
convert' (Casl.UPast' phi psi)      =  liftM2 Ltl.S   (convert' phi) (convert' psi)
convert' (Casl.BPast' phi psi)      =  convert'       ((Casl.Pnot psi) `Casl.UPast'` (phi `Casl.Pand` (Casl.Pnot psi)))

convert' (Casl.XPast' phi)          =  liftM  Ltl.Z   (convert' phi)

convert' _                          =  Nothing


{------------------------------------------------------------------------------}


data Expr = Expr String

instance Show Expr where show (Expr x) = x

expr = liftM Expr (many1 (lower <|> char '=' <|> char '_' <|> char '.' <|> digit))

parseAndConvert :: String -> Formula Expr
parseAndConvert text = let Right x = parse (Casl.parser expr) "<<input>>" text in
                       let Just y  = convert x in
                       y



{------------------------------------------------------------------------------}
