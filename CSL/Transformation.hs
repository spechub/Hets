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
import qualified Data.Map as Map
import Data.Maybe 
import Prelude hiding (lookup)

import CSL.Interpreter
import CSL.AS_BASIC_CSL
import CSL.Parse_AS_Basic
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

instance VarGen m => VarGen (StateT s m) where
    genVar = lift genVar


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
    toExp s = mkAndAnalyzeOp s [] [] nullRange

instance SExp a => SExp (String, a) where
    toExp (s, x) = mkAndAnalyzeOp s [] [toExp x] nullRange

instance (SExp a, SExp b) => SExp (String, a, b) where
    toExp (s, x, y) = mkAndAnalyzeOp s [] [toExp x, toExp y] nullRange

instance (SExp a, SExp b, SExp c) => SExp (String, a, b, c) where
    toExp (s, x, y, z) =
        mkAndAnalyzeOp s [] [toExp x, toExp y, toExp z] nullRange


-- strangely, ghc says that we would have overlapping instances with 
-- instance SExp a => SExp (String, a), but I can't see it. I introduce
-- this strange looking instance
instance (SExp a) => SExp ((), String, [a]) where
    toExp (_, s, l) = mkAndAnalyzeOp s [] (map toExp l) nullRange

-- | A class to construct CMDs from simple tuple structures
class SCmd a where
    toCmd :: a -> CMD

instance (SExp a, SExp b) => SCmd (String, a, b) where
    toCmd (s, x, y) = Cmd s [toExp x, toExp y]

instance (SExp a, SExp b) => SCmd (a, b) where
    toCmd (x, y) = Ass (toExp x) $ toExp y

type VarRange = (APFloat, APFloat)

class IntervalLike a where
    toIntervalExp :: a -> EXPRESSION

instance IntervalLike EXPRESSION where
    toIntervalExp = id

instance IntervalLike VarRange where
    toIntervalExp (a, b) = Interval a b nullRange

-- ----------------------------------------------------------------------
-- * Transformations of assignments to conditional statements
-- ----------------------------------------------------------------------


-- ** A simple cache implemenation with variable container
-- | We store all results from the backup lookup in the map, even the negative
-- ones (Nothing returned).
-- backupLookup is set once the data is created, the cachemap and varcontainer
-- are updated afterwards.
data VCCache = VCCache { varcontainer :: Map.Map String VarRange
                       , cachemap :: Map.Map String (Maybe EXPRESSION) } deriving Show

lookupCached :: MonadState VCCache m => (String -> m (Maybe EXPRESSION)) -> String
             -> m (Maybe EXPRESSION)
lookupCached = lookupCachedWithTrans return

lookupCachedWithTrans :: MonadState VCCache m =>
                          (EXPRESSION -> m EXPRESSION) -- ^ Transformation function
                      ->  (String -> m (Maybe EXPRESSION)) -- ^ lookup function
                      -> String -- ^ lookup key
                      -> m (Maybe EXPRESSION) -- ^ lookuped and transformed result
lookupCachedWithTrans f lk k = do
  c <- get
  case Map.lookup k (cachemap c) of
    Nothing ->  do
      mV <- lk k
      mV' <- case mV of
               Just v -> f v >>= return . Just
               _ -> return Nothing
      -- f can change the state, so read it again here!
      c' <- get
      put c' { cachemap = Map.insert k mV' (cachemap c') }
      return mV'
    Just mV -> return mV

resetCache :: Monad m => VCCache -> m VCCache
resetCache c = return c{ cachemap = Map.empty }

-- | Given a lookupfunction we initialize the VCCache
emptyVCCache :: VCCache
emptyVCCache = VCCache Map.empty Map.empty


class VariableContainer a b where
    insertVar :: String -> b -> a -> a
    toVarList :: a -> [(String, b)]

instance VariableContainer VCCache VarRange where
    insertVar s v c = c { varcontainer = Map.insert s v $ varcontainer c }
    toVarList = Map.toList . varcontainer

-- | If the state of a statemonad is a VariableContainer then we provide a
--  simplified insert function, which hides the state handling
insertVarM :: (Monad m, VariableContainer a b) => String -> b -> StateT a m ()
insertVarM s iRng = fmap (insertVar s iRng) get >>= put

-- | If the state of a statemonad is a VariableContainer then we provide a
--  simplified insert function, which hides the state handling
toVarListM :: (VariableContainer a b, Monad m) => StateT a m [(String, b)]
toVarListM = fmap toVarList get


-- | Given an expression containing intervals we code out the intervals
--   replacing them by variables and assign to those variables ranges
--   (the intervals). Does not replace toplevel intervals.
replaceIntervals ::
    (VarGen c, VariableContainer a VarRange, CalculationSystem c) =>
    EXPRESSION -> StateT a c EXPRESSION
replaceIntervals e@(Interval _ _ _) = return e
replaceIntervals e = replaceIntervals' e

-- | Like replaceIntervals but works also on toplevel intervals
replaceIntervals' ::
    (VarGen c, VariableContainer a VarRange, CalculationSystem c) =>
    EXPRESSION -> StateT a c EXPRESSION
replaceIntervals' e = 
    case e of
      Interval from to rg -> do
             y <- genVar
             insertVarM y (from, to)
             return $ Var $ Token y rg
      Op s epl args rg -> do
             nargs <- mapM replaceIntervals' args
             return $ Op s epl nargs rg
      List elms rg -> do
             nelms <- mapM replaceIntervals' elms
             return $ List nelms rg
      _ -> return e

-- TODO: add support for function terms
-- | Replaces all occurrences of defined variables by their lookuped terms
substituteDefined :: ( VarGen c, CalculationSystem c)
                    => EXPRESSION -> StateT VCCache c EXPRESSION
substituteDefined x =
    case x of
      Op oi epl args rg -> do
             let (s, isOpName) = case oi of
                                   OpId _ -> ("", True)
                                   OpString os -> (os, False)
             b <- if isOpName then return False else isDefined s
             nargs <- mapM substituteDefined args
             if b && null args
              then do
                mE <- lookupCachedWithTrans replaceIntervals lookup s
                case mE of
                  Just (Interval from to _) ->
                      do
                        -- enter the interval into the VariableContainer
                        insertVarM s (from, to)
                        return x
                  Just e -> return e
                  _ -> error "substituteDefined: defined constant not found"
              else return $ Op oi epl nargs rg
      List elms rg -> do
             nelms <- mapM substituteDefined elms
             return $ List nelms rg
      _ -> return x


buildConditionalExpression :: VCCache -> EXPRESSION -> EXPRESSION
buildConditionalExpression vcc e =
    let condlist = map (uncurry toIntervalCondition)
                   $ Map.toList $ varcontainer vcc
    in case condlist of
         [] -> e
         [c] -> toExp ("impl", c, e)
         _ -> toExp ("impl", toExp ((), "and", condlist), e)

toIntervalCondition :: (SExp e, IntervalLike i) => e -> i -> EXPRESSION
toIntervalCondition e i = toExp ("in", e, toIntervalExp i)

-- | Produces a verification condition for the given Assignment c := t
verificationCondition :: ( VarGen c, CalculationSystem c)
                         => EXPRESSION -- ^ the lookuped value of a constant
                         -> EXPRESSION -- ^ the definiens of this constant
                         -> c EXPRESSION -- ^ the conditional statement,
                                         -- conditional in occurring interval
                                         -- variables
verificationCondition c e = do
  (_, vcc1) <- runStateT (replaceIntervals c) emptyVCCache
  (e', vcc2) <- runStateT (substituteDefined e >>= replaceIntervals')
                emptyVCCache

  -- 1. c is an interval -> vcc2 => e' in c
  -- 2. c contains intervals -> error, don't know how to build conditional
  -- 3. e contains intervals -> error, can't bound interval expression by constant
  -- 4. otherwise ->  e' = c
  case c of
    Interval _ _ _ -> 
        do 
          let vericond = toIntervalCondition e' c
          return $ buildConditionalExpression vcc2 vericond
    _ | not $ Map.null $ varcontainer vcc1 ->
          error $ "verificationCondition: don't know how to build conditional"
                    ++ "from interval expression"
      | not $ Map.null $ varcontainer vcc2 ->
          error $ "verificationCondition:  can't bound interval expression by"
                    ++ "constant"
      | otherwise -> return $ toExp ("=", e', c)



-- ----------------------------------------------------------------------
-- * Transformations for Repeat
-- ----------------------------------------------------------------------

-- | Transforms a repeat command using the convergence predicate in a repeat
-- command where the body and the condition are extended by some intermediate
-- variables and their assignments
transRepeat :: VarGen m =>  EXPRESSION -> [CMD] -> m CMD
transRepeat e cl = do
    (l, e') <- transRepeatCondition e
    let f (v1, v2, tm) = (toCmd (v1, v2), toCmd (v2, tm))
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
      Op (OpId OP_convergence) [] [lt, tm] _ -> do
             v1 <- genVar
             v2 <- genVar
             return ([(v1, v2, tm)], transConvergence v1 v2 lt)
      Op oi@(OpId on) [] al rg
          | elem on [OP_and, OP_or] -> do
             l <- mapM transRepeatCondition al
             let (ssel, el) = unzip l
             return (concat ssel, Op oi [] el rg)
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
