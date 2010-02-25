{- |
Module      :  $Header$
Description :  matching of terms modulo definition expansion
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  portable

matching of terms modulo constant definition expansion and constraints
-}

module HasCASL.MatchingWithDefinitions where

import HasCASL.Subst

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.FoldTerm
import HasCASL.Le

import Common.Id
import Common.Lib.State

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List as List
import Data.Maybe

import Control.Monad

------------------------- Preliminaries -------------------------

{-
  
* OVERVIEW OF THE ALGORITHM

Input: 
- map = constant->term mapping for constant definition expansion
- noclash = a function taking two constants which produced a clash
            and returning whether or not this clash should be ignored and
            the corresponding term-pair should be added to the constraints
- t1 = term pattern
- t2 = concrete term to be matched against the pattern


Output:
a lazy list of:
- s = a substitution containing the equalities which make the pattern and the term equal
- cstr = constraint list of equalities which have to be satisfied: in the case
         where a constant in t2 is encountered which cannot be expanded, but the corresponding pattern
         part is still not atomic, or where we get a clash between non-constructor terms

-}


----------------------- simple matching -----------------------

--isConstructor :: OpInfo -> Bool
{-
  The default behaviour of the match is to signal only a clash
  if two constructors that are different are tried to be matched.
  For that reason we provide a facility for extracting the testfunctions
  from a HasCASL signature.
-}

getConstructors :: Assumps -> Map.Map Id (Set.Set TypeScheme)
getConstructors a = let constrs = Map.map (Set.filter isConstructor) a
                    in Map.map (Set.map opType) 
                       $ Map.filter (not . Set.null) constrs


match :: (Monad m) => Subst -> (Term -> Term -> Bool) -> (Term -> Term -> Bool)
      -> Term -> Term -> m (Subst, [(Term, Term)])
match map noclashHead noclash t1 t2 =
    matchAux map noclashHead noclash (eps, []) (t1, t2)


matchAux :: (Monad m) => Subst -> (Term -> Term -> Bool)
         -> (Term -> Term -> Bool) -> (Subst, [(Term, Term)]) -> (Term, Term)
         -> m (Subst, [(Term, Term)])
matchAux map noclashHead noclash output@(sbst, ctrts) terms@(t1, t2) =
    case terms of
      -- handle the skip-cases first
      (TypedTerm term _ _ _, _) -> match' term t2
      (_, TypedTerm term _ _ _) -> match' t1 term

      -- check for clash, handle constraints and definition expansion
      (ApplTerm f1 a1 _, _) ->
          case t2 of
            ApplTerm f2 a2 _ | f1 == f2 -> match' a1 a2
                             | noclashHead f1 f2 -> addConstraint t1 t2
            _ -> tryDefExpand

      (TupleTerm l _, _) -> 
          case t2 of
            TupleTerm l' _ | length l == length l' ->
                               foldM matchF output $ zip l l'
                           | otherwise -> tupleClash l l'
            _ -> tryDefExpand

      -- add the mapping v->t2 to output
      (QualVar v, _) -> addMapping v t2
      -- add the mapping (n,typ)->t2 to output
      (QualOp _ n typ _ _ _, _) -> addMapping (n,typ) t2

      -- all other terms are not expected and accepted here
      _ -> fail "matchAux: unhandled term"

      where matchF = matchAux map noclashHead noclash -- used for the fold
            match' = curry $ matchF output
            addMapping k t =
                let sc = toSC k in
                case lookupContent sbst sc of
                  Just t' | t == t' -> return output
                          | otherwise -> fail
                                         $ concat [ "matchAux: "
                                                  , "Conflicting substitution"
                                                  , " for ", show k]
                  _ -> return (addTerm sbst sc t, ctrts)
            addConstraint t t' = return (sbst, (t,t'):ctrts)
            -- The definition expansion application case
            -- (for ApplTerm and TupleTerm) is handled uniformly
            tryDefExpand = case defExpansion t2 of
                             Just t2' -> match' t1 t2'
                             _ | noclash t1 t2 -> addConstraint t1 t2
                               | otherwise -> clash


            defExpansion = lookupContent map
            clash = fail $ "matchAux: Clash for " ++ show (t1,t2)
            tupleClash l l' = fail $ "matchAux: Clash for tuples "
                              ++ show (l, l')


