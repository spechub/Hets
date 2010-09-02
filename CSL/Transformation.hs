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

import Control.Monad.State (State, get, put)
import qualified Data.Set as Set

import CSL.Interpreter
import CSL.AS_BASIC_CSL
import Common.Id (nullRange)

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

data AssContainer = AssContainer { definedConstants :: Set.Set String
                                 , varCounter :: Int }


instance VarGen (State AssContainer) where
    genVar = do
      c <- get
      put c { varCounter = varCounter c + 1 }
      return $ "." ++ show (varCounter c)

instance AssignmentContainer (State AssContainer) where
    isDefined s = get >>= return . Set.member s . definedConstants


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
