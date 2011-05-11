{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
{- |
Module      :  $Header$
Description :  Program transformations
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  non-portable (various glasgow extensions)

Program transformations from CSL specifications to CAS programs
and utilities for lemma generation

-}

module CSL.Transformation where

import Control.Monad.State (State, StateT(..), MonadState(get, put))
import Control.Monad.Trans (lift)
import Prelude hiding (lookup)

import CSL.AS_BASIC_CSL
import CSL.ASUtils
import Common.Id

-- ----------------------------------------------------------------------
-- * Datatypes and Classes for Term- and Program Transformations
-- ----------------------------------------------------------------------


mkOperator :: String -> [EXTPARAM] -> [EXPRESSION] -> Range -> EXPRESSION
mkOperator = mkAndAnalyzeOp ()

-- | A class to abstract from the concrete variable generation facility
class Monad m => VarGen m where
    genVar :: m (String)

instance VarGen (State Int) where
    genVar = do
      i <- get
      put $ i+1
      return $ "gv" ++ show i

instance VarGen (State (Int, String)) where
    genVar = do
      (i, s) <- get
      put $ (i+1, s)
      return $ s ++ show i

instance VarGen m => VarGen (StateT s m) where
    genVar = lift genVar


-- | A class to construct EXPRESSIONs from simple tuple structures
class SExp a where
    toExp :: a -> EXPRESSION

class SOp a where
    toOp :: a -> OpDecl

instance SExp EXPRESSION where
    toExp e = e

instance SExp APInt where
    toExp i = Int i nullRange

instance SExp APFloat where
    toExp f = Rat f nullRange

instance SExp String where
    toExp s = mkOperator s [] [] nullRange

instance SOp String where
    toOp s = OpDecl (SimpleConstant s) [] [] nullRange

instance SExp OPNAME where
    toExp n = mkPredefOp n []

instance SExp ConstantName where
    toExp (SimpleConstant s) = mkOperator s [] [] nullRange
    toExp x = error $ "toExp: elim-constant not supported " ++ show x

instance SExp a => SExp (String, a) where
    toExp (s, x) = mkOperator s [] [toExp x] nullRange

instance SExp a => SExp (ConstantName, [a]) where
    toExp (n, l) = Op (OpUser n) [] (map toExp l) nullRange

instance (SExp a, SExp b) => SExp (String, a, b) where
    toExp (s, x, y) = mkOperator s [] [toExp x, toExp y] nullRange

instance (SExp a, SExp b, SExp c) => SExp (String, a, b, c) where
    toExp (s, x, y, z) =
        mkOperator s [] [toExp x, toExp y, toExp z] nullRange


-- strangely, ghc says that we would have overlapping instances with 
-- instance SExp a => SExp (String, a), but I can't see it. I introduce
-- this strange looking instance
instance (SExp a) => SExp ((), String, [a]) where
    toExp (_, s, l) = mkOperator s [] (map toExp l) nullRange

-- | A class to construct CMDs from simple tuple structures
class SCmd a where
    toCmd :: a -> CMD

instance (SExp a, SExp b) => SCmd (String, a, b) where
    toCmd (s, x, y) = Cmd s [toExp x, toExp y]

instance (SOp a, SExp b) => SCmd (a, b) where
    toCmd (x, y) = Ass (toOp x) $ toExp y

class IntervalLike a where
    toIntervalExp :: a -> EXPRESSION

instance IntervalLike EXPRESSION where
    toIntervalExp = id

instance IntervalLike (Double, Double) where
    toIntervalExp (a, b) = Interval a b nullRange

