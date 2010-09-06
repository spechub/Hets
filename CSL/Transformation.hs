{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
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

import Control.Monad.State (State, StateT(..), MonadState(get, put))
import Control.Monad.Trans (lift)
import Control.Monad (when)
import qualified Data.Map as Map
import Data.Maybe 
import Prelude hiding (lookup)

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

-- | A cache with lookup, lookupWithTransformation and reset
class Monad m => Cache m a b c | a -> b c where
    lookupCachedWithTrans :: (c -> m c) -> b -> a -> m (Maybe c, Maybe a)
    -- ^ like lookupCached, but before writing the result to the cache transform
    -- it with the given function
    lookupCached :: b -> a -> m (Maybe c, Maybe a)
    -- ^ if the value is not already cached lookup the value in the original
    -- store and write the result to the cache, otherwise use the value in
    -- the cache.
    lookupCached = lookupCachedWithTrans return
    resetCache :: a -> m a -- ^ remove all cached entries

-- ** A simple Cache implemenation
-- | We store all results from the backup lookup in the map, even the negative
-- ones (Nothing returned).
-- backupLookup and cacheWriteback are set once the data is created, only
-- the cachemap is updated afterwards.
data SimpleCache m a b = SimpleCache { cachemap :: Map.Map a (Maybe b)
                                     , backupLookup :: a -> m (Maybe b) }

instance (Monad m, Ord a) => Cache m (SimpleCache m a b) a b where
    lookupCachedWithTrans f k c =
        case Map.lookup k (cachemap c) of
          Nothing ->  do
            mV <- backupLookup c k
            mV' <- case mV of
                     Just v -> f v >>= return . Just
                     _ -> return Nothing
            return (mV', Just c { cachemap = Map.insert k mV' (cachemap c) })
          Just mV -> return (mV, Nothing)
    resetCache c = return c{ cachemap = Map.empty }

instance Cache m a b c => Cache (StateT a m) a b c where
    lookupCachedWithTrans f k = error "" -- lift . lookupCachedWithTrans f k
    resetCache = lift . resetCache

type VarRange = (APFloat, APFloat)

-- | A variable-range-container datatype
type VRC = Map.Map String VarRange


class VariableContainer a b where
    insertVar :: String -> b -> a -> a
    toVarList :: a -> [(String, b)]

instance VariableContainer (Map.Map String a) a where
    insertVar = Map.insert
    toVarList = Map.toList

-- | Type to combine a variable container and a variable cache
data VCCache m = VCCache { varcontainer :: Map.Map String VarRange
                         , varcache :: SimpleCache m String EXPRESSION }

-- | Given a lookupfunction we initialize the VCCache
initVCCache :: (String -> m (Maybe EXPRESSION)) -> VCCache m
initVCCache f = VCCache Map.empty $ SimpleCache Map.empty f

-- | If VCCache is over a CalculationSystem we use its lookup function for init
csVCCache :: CalculationSystem m => m (VCCache m)
csVCCache = return $ initVCCache lookup

instance VariableContainer (VCCache m) VarRange where
    insertVar s v c = c { varcontainer = insertVar s v $ varcontainer c }
    toVarList = toVarList . varcontainer

instance Monad m => Cache m (VCCache m) String EXPRESSION where
    lookupCached k c = do
      (mE, mC) <- lookupCached k $ varcache c
      return (mE, fmap ( \ x -> c { varcache = x } ) mC)
    resetCache = error "resetCache: not implemented for VCCache"


-- | If the state of a statemonad is a VariableContainer then we provide a
--  simplified insert function, which hides the state handling
insertVarM :: (VariableContainer a b, Monad m) => String -> b -> StateT a m ()
insertVarM s iRng = fmap (insertVar s iRng) get >>= put

-- | If the state of a statemonad is a VariableContainer then we provide a
--  simplified insert function, which hides the state handling
toVarListM :: (VariableContainer a b, Monad m) => StateT a m [(String, b)]
toVarListM = fmap toVarList get

instance VarGen m => VarGen (StateT s m) where
    genVar = lift genVar

-- | If the state of a statemonad is a simple cache then we provide a simplified
-- lookup function, which hides the state handling
lookupInStateCache :: (Cache m a b c, MonadState a m) =>
                      b -> m (Maybe c)
lookupInStateCache s = do
  st <- get
  (mE, mSt) <- lookupCached s st
  when (isJust mSt) $ put $ fromJust mSt
  return mE

-- | Given an expression containing intervals we code out the intervals
--   replacing them by variables and assign to those variables ranges
--   (the intervals).
replaceIntervals ::
    (VarGen c, VariableContainer a VarRange, CalculationSystem c) =>
    EXPRESSION -> StateT a c EXPRESSION
replaceIntervals e = 
    case e of
      Interval from to rg -> do
             y <- genVar
             insertVarM y (from, to)
             return $ Var $ Token y rg
      Op s epl args rg -> do
             nargs <- mapM replaceIntervals args
             return $ Op s epl nargs rg
      List elms rg -> do
             nelms <- mapM replaceIntervals elms
             return $ List nelms rg
      _ -> return e

-- TODO: we have to integrate the interval replacing into the substitution in
-- order to minimize the number of new variables introduced, consider, e.g.,
--   e = x*(x+1)
-- and x = [1, 1.01] in the environment
-- we would get e' = [1, 1.01]*([1, 1.01] + 1) and if we now replace intervals
-- we get e'' = x1*(x2+1) with x1 = [1, 1.01] and x2 = [1, 1.01]
-- The other way arround we would lookup once the x replace it with x1, and put
-- x1 in [1, 1.01] to the conditionals-mapping
-- | Replaces all occurrences of defined variables by their lookuped terms
substituteDefined :: ( VarGen c, VariableContainer a VarRange
                     , CalculationSystem c, Cache c a String EXPRESSION)
                    => EXPRESSION -> StateT a c EXPRESSION
substituteDefined x =
    case x of
      Op s epl args rg -> do
             b <- isDefined s
             nargs <- mapM substituteDefined args
             if b && null args
              then do
                mE <- lookupInStateCache s
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
