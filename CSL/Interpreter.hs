{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
{- |
Module      :  $Header$
Description :  Interpreter for CPL programs
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  portable

Defines an interface for Calculators used to evaluate CPL programs
-}

module CSL.Interpreter where

import Data.Maybe
import qualified Data.Map as Map
import CSL.AS_BASIC_CSL

-- * Evaluator

-- | calculation interface, bundles the evaluation engine and the constant store
class Monad m => CalculationSystem m a where
    assign :: a -> String -> EXPRESSION -> m a
    clookup :: a -> String -> m (Maybe EXPRESSION)
    names :: a -> m [String]
    eval :: EXPRESSION -> a -> m EXPRESSION
    values :: a -> m [(String, EXPRESSION)]
    values cs = let f x = do
                      v <- clookup cs x
                      return (x, fromJust v)
                in names cs >>= mapM f

instance Monad m => CalculationSystem m (Map.Map String EXPRESSION) where
    assign c n e = return $ Map.insert n e c
    clookup c n = return $ Map.lookup n c
    names = return . Map.keys
    eval e = return . const e


