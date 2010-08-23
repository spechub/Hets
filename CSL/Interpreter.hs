{-# LANGUAGE FlexibleInstances #-}
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

import Control.Monad (liftM, forM_, filterM, unless)
import Control.Monad.State (State, MonadState (..))
import Data.Maybe
import qualified Data.Map as Map
import CSL.AS_BASIC_CSL

-- ----------------------------------------------------------------------
-- * Evaluator
-- ----------------------------------------------------------------------

-- | calculation interface, bundles the evaluation engine and the constant store
class Monad m => CalculationSystem m where
    assign :: String -> EXPRESSION -> m () -- evtl. m Bool instead as success-flag
    clookup :: String -> m (Maybe EXPRESSION)
    names :: m [String]
    eval :: EXPRESSION -> m EXPRESSION
    check :: EXPRESSION -> m Bool
    check = error "CalculationSystem-default: 'check' not implemented."
    values :: m [(String, EXPRESSION)]
    values = let f x = do
                   v <- clookup x
                   return (x, fromJust v)
             in names >>= mapM f

-- | Just an example which does not much, for illustration purposes
instance CalculationSystem (State (Map.Map String EXPRESSION)) where
    assign n e = liftM (Map.insert n e) get >> return ()
    clookup n = liftM (Map.lookup n) get
    names = liftM Map.keys get
    eval e = return e
    check _ = return False

destructureAssignment :: CMD -> Maybe (String, EXPRESSION)
destructureAssignment (Cmd ":=" [Op n [] [] _, e]) = Just (n, e)
destructureAssignment _ = Nothing

destructureConstraint :: CMD -> Maybe EXPRESSION
destructureConstraint (Cmd "constraint" [e]) = Just e
destructureConstraint _ = Nothing

evaluate :: CalculationSystem m => CMD -> m ()
evaluate (Cmd ":=" [Op n [] [] _, e]) = assign n e
evaluate (Cond l) = do
  cl <- filterM (check . fst) l
  if null cl
    then error "evaluate: non-exhaustive conditional"
    else evaluateList $ snd $ head cl
evaluate (Repeat e l) =
    let f = do
          -- first run of the repeat loop
          evaluateList l
          b <- check e
          -- repeat f until condition holds
          unless b f
    in f
evaluate (Cmd c _) = error $ "evaluate: unsupported command " ++ c


evaluateList :: CalculationSystem m => [CMD] -> m ()
evaluateList l = forM_ l evaluate

