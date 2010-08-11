{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Program transformations
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  portable

Program transformations from CSL specifications to CAS programs

-}

module CSL.Transformation
    ( transConvergence
    , transRepeatCondition
    , transRepeat
    , SExp(..)
    , SCmd(..)
    )
    where

import CSL.AS_BASIC_CSL
import Common.Id (nullRange)
import Data.List


-- * Transformations for Repeat

-- | A class to abstract from the concrete variable generation facility
class VarGen a where
    genVar :: a -> (a, String)

instance VarGen Int where
    genVar i = (i+1, "gv" ++ show i)

instance VarGen (Int, String) where
    genVar (i, s) = ((i+1, s), s ++ show i)

-- | A class to construct EXPRESSIONs from simple tuple structures
class SExp a where
    toExp :: a -> EXPRESSION

instance SExp EXPRESSION where
    toExp e = e

instance SExp Int where
    toExp i = Int i nullRange

instance SExp Float where
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


-- This function can be used, e.g., to adjust a function for use with mapAccum
tripleToPair :: (a -> (b, c, d)) -> a -> (b, (c, d))
tripleToPair f x = let (s, t, u) = f x in (s, (t, u))

-- | Transforms a repeat command using the convergence predicate in a repeat
-- command where the body and the condition are extended by some intermediate
-- variables and their assignments
transRepeat :: VarGen a => a -> EXPRESSION -> [CMD] -> (a, CMD)
transRepeat g e cl =
    let (g', l, e') = transRepeatCondition g e
        f (v1, v2, tm) = (toCmd (":=", v1, v2), toCmd (":=", v2, tm))
        (l1, l2) = unzip $ map f l
    in (g', Repeat e' $ l1 ++ cl ++ l2)

-- | Replaces the convergence expressions in the repeat condition using the
-- transConvergence function
transRepeatCondition :: VarGen a => a -- ^ A generator for intermediate vars
                     -> EXPRESSION -- ^ The repeat condition
                     -> (a, [(String, String, EXPRESSION)], EXPRESSION)
                        -- ^ The updated generator, a list of intermediate
                        -- convergence vars together with the term to converge
                        -- and the translated repeat condition
transRepeatCondition g c =
    let f a = tripleToPair $ transRepeatCondition a
    in case c of
         Op "convergence" [] [lt, tm] _ ->
             let (g', v1) = genVar g
                 (g'', v2) = genVar g'
             in (g'', [(v1, v2, tm)], transConvergence v1 v2 lt)
         Op o [] al rg
             | elem o ["and", "or"] ->
                 let (g', l) = mapAccumL f g al
                     (ssel, el) = unzip l
                 in (g', concat ssel, Op o [] el rg)
             | otherwise -> (g, [], c)
         _ -> (g, [], c)


-- | Returns the the program expression for the convergence predicate.
transConvergence :: String -- ^ The variable name to store the preceeding value
                 -> String -- ^ The variable name to store the current value
                 -> EXPRESSION -- ^ The numerical expression for the limit
                 -> EXPRESSION -- ^ A nested if-expression corresponding to the
                               -- convergence expression

transConvergence v1 v2 lt =
    toExp (    "if", ("not", ("numberp", v1)), "false"
          ,(   "if", ("neq", v2, 0::Int)
           ,(         "<", ("abs", ("/", ("-", v1, v2), v2)), lt)
           ,(  "if", ("eq", v1, 0::Int),       "true", "false")))
