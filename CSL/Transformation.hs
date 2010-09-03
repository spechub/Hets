{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
{- |
Module      :  $Header$
Description :  Program transformations
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  portable

Program transformations from CSL specifications to CAS programs
and utilities for lemma generation

-}

module CSL.Transformation where

import Control.Monad.State (StateT(..), State, get, put)
import Control.Monad.Trans (lift)
import qualified Data.Map as Map

import CSL.Interpreter
import CSL.AS_BASIC_CSL
import Common.Id (nullRange, Token(..))

-- ----------------------------------------------------------------------
-- * Datatypes and Classes for Term- and Program Transformations
-- ----------------------------------------------------------------------

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


class Monad m => AssignmentContainer m where
    isDefined :: String -> m Bool

class Monad m => VariableRangeContainer m where
    addVarRange :: String -> (APFloat, APFloat) -> m ()
    getVarRanges :: m [(String, (APFloat, APFloat))]


-- | A class to construct EXPRESSIONs from simple tuple structures
class SExp a where
    toExp :: a -> EXPRESSION

instance SExp EXPRESSION where
    toExp e = e

instance SExp APInt where
    toExp i = Int i nullRange

instance SExp APFloat where
    toExp f = Double f nullRange

instance SExp String where
    toExp s = Op s [] [] nullRange

instance SExp a => SExp (String, a) where
    toExp (s, x) = Op s [] [toExp x] nullRange

instance (SExp a, SExp b) => SExp (String, a, b) where
    toExp (s, x, y) = Op s [] [toExp x, toExp y] nullRange

instance (SExp a, SExp b, SExp c) => SExp (String, a, b, c) where
    toExp (s, x, y, z) = Op s [] [toExp x, toExp y, toExp z] nullRange

-- | A class to construct CMDs from simple tuple structures
class SCmd a where
    toCmd :: a -> CMD

instance (SExp a, SExp b) => SCmd (String, a, b) where
    toCmd (s, x, y) = Cmd s [toExp x, toExp y]

-- ----------------------------------------------------------------------
-- * Transformations of assignments to conditional statements
-- ----------------------------------------------------------------------

type VRC = Map.Map String (APFloat, APFloat)

instance VarGen m => VarGen (StateT s m) where
    genVar = lift genVar

instance Monad m => VariableRangeContainer (StateT VRC m)
    where
      addVarRange s iRng = fmap (Map.insert s iRng) get >>= put
      getVarRanges = fmap Map.toList get


-- | Given an expression containing intervals we code out the intervals
--   replacing them by variables and assign to those variables ranges
--   (the intervals).
replaceIntervals :: (VarGen c, CalculationSystem c) =>
                    VRC -> EXPRESSION -> c (EXPRESSION, VRC)
replaceIntervals s e = runStateT (replaceIntervals' e) s

replaceIntervals' :: (VarGen m, VariableRangeContainer m) =>
                    EXPRESSION -> m EXPRESSION
replaceIntervals' x =
    case x of
      Interval from to rg -> do
             y <- genVar
             addVarRange y (from, to)
             return $ Var $ Token y rg
      Op s epl args rg -> do
             nargs <- mapM replaceIntervals' args
             return $ Op s epl nargs rg
      List elms rg -> do
             nelms <- mapM replaceIntervals' elms
             return $ List nelms rg
      _ -> return x

-- TODO: we have to integrate the interval replacing into the substitution in
-- order to minimize the number of new variables introduced, consider, e.g.,
--   e = x*(x+1)
-- and x = [1, 1.01] in the environment
-- we would get e' = [1, 1.01]*([1, 1.01] + 1) and if we now replace intervals
-- we get e'' = x1*(x2+1) with x1 = [1, 1.01] and x2 = [1, 1.01]
-- The other way arround we would lookup once the x replace it with x1, and put
-- x1 in [1, 1.01] to the conditionals-mapping
-- | Replaces all occurrences of defined variables by their lookuped terms
substituteDefined :: (AssignmentContainer c, CalculationSystem c) =>
                     EXPRESSION -> c EXPRESSION
substituteDefined x =
    case x of
      Op s epl args rg -> do
             b <- isDefined s
             nargs <- mapM substituteDefined args
             if b && null args
              then do
                mE <- lookupCache >>= lookupCached s
                case mE of
                  Just e -> return e
                  _ -> error "substituteDefined: defined constant not found"
              else return $ Op s epl nargs rg
      List elms rg -> do
             nelms <- mapM substituteDefined elms
             return $ List nelms rg
      _ -> return x


-- ----------------------------------------------------------------------
-- * Transformations for Repeat
-- ----------------------------------------------------------------------

-- | Transforms a repeat command using the convergence predicate in a repeat
-- command where the body and the condition are extended by some intermediate
-- variables and their assignments
transRepeat :: VarGen m =>  EXPRESSION -> [CMD] -> m CMD
transRepeat e cl = do
    (l, e') <- transRepeatCondition e
    let f (v1, v2, tm) = (toCmd (":=", v1, v2), toCmd (":=", v2, tm))
        (l1, l2) = unzip $ map f l
    return $ Repeat e' $ l1 ++ cl ++ l2

-- | Replaces the convergence expressions in the repeat condition using the
-- transConvergence function
transRepeatCondition :: VarGen m => EXPRESSION -- ^ The repeat condition
                     -> m ([(String, String, EXPRESSION)], EXPRESSION)
                        -- ^ A list of intermediate convergence vars together
                        --  with the term to converge and the translated repeat
                        --  condition
transRepeatCondition c =
    case c of
      Op "convergence" [] [lt, tm] _ -> do
             v1 <- genVar
             v2 <- genVar
             return ([(v1, v2, tm)], transConvergence v1 v2 lt)
      Op o [] al rg
          | elem o ["and", "or"] -> do
             l <- mapM transRepeatCondition al
             let (ssel, el) = unzip l
             return (concat ssel, Op o [] el rg)
          | otherwise -> return ([], c)
      _ -> return ([], c)


-- | Returns the the program expression for the convergence predicate.
transConvergence :: String -- ^ The variable name to store the preceeding value
                 -> String -- ^ The variable name to store the current value
                 -> EXPRESSION -- ^ The numerical expression for the limit
                 -> EXPRESSION -- ^ A nested if-expression corresponding to the
                               -- convergence expression

transConvergence v1 v2 lt =
    toExp (    "if", ("not", ("numberp", v1)), "false"
          ,(   "if", ("neq", v2, 0::Integer)
           ,(         "<", ("abs", ("/", ("-", v1, v2), v2)), lt)
           ,(  "if", ("eq", v1, 0::Integer),       "true", "false")))
