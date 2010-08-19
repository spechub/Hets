{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
{- |
Module      :  $Header$
Description :  Interpreter for CPL programs
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  portable

Defines an interface for Calculators used to evaluate CPL programs
-}

module CSL.Interpreter where

import Control.Monad (liftM, forM_)
import Control.Monad.State (State, MonadState (..))
import Data.Maybe
import qualified Data.Map as Map
import CSL.AS_BASIC_CSL

-- * Evaluator

-- | calculation interface, bundles the evaluation engine and the constant store
class Monad m => CalculationSystem m where
    assign :: String -> EXPRESSION -> m () -- evtl. m Bool instead as success-flag
    clookup :: String -> m (Maybe EXPRESSION)
    names :: m [String]
    eval :: EXPRESSION -> m EXPRESSION
    values :: m [(String, EXPRESSION)]
    values = let f x = do
                   v <- clookup x
                   return (x, fromJust v)
             in names >>= mapM f

-- | Just an example which does not much... 
instance CalculationSystem (State (Map.Map String EXPRESSION)) where
    assign n e = liftM (Map.insert n e) get >> return ()
    clookup n = liftM (Map.lookup n) get
    names = liftM Map.keys get
    eval e = return e

destructureAssignment :: CMD -> Maybe (String, EXPRESSION)
destructureAssignment (Cmd ":=" [Op n [] [] _, e]) = Just (n, e)
destructureAssignment _ = Nothing

evaluate :: CalculationSystem m => CMD -> m ()
evaluate c = case destructureAssignment c of
                  Just (n, e) -> assign n e
                  _ -> error $ "evaluate: non-assignment: " ++ show c

evaluateList :: CalculationSystem m => [CMD] -> m ()
evaluateList l = forM_ l evaluate
