{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Program transformations
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  portable

Program transformations from CSL specifications to CAS programs

-}

module CSL.Transformation
    ( mytest
    , transConvergence
    , SExp(..)
--    , toExp
    )
    where

import CSL.AS_BASIC_CSL
import Common.Id (nullRange)


-- * Transformations for Repeat
class SExp a where
    toExp :: a -> EXPRESSION

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


mytest :: EXPRESSION
mytest = toExp ("+", ("hallo", 1::Int), "333ta")

-- | Returns the the program expression for the convergence predicate.
transConvergence :: String -- ^ the variable name to store the
                 -> String -- ^
                 -> EXPRESSION -- ^
                 -> EXPRESSION -- ^
                 -> EXPRESSION -- ^

transConvergence v1 v2 lt tm = error ""
