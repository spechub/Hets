{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  matching of terms modulo definition expansion
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  portable

matching of terms modulo constant definition expansion and constraints
-}

module HasCASL.MatchingWithDefinitions where

import HasCASL.Subst

import HasCASL.As
import HasCASL.Le
import HasCASL.PrintAs

import Common.Id
import Common.DocUtils

import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Monad



{-
  Simple matching:

  The default behaviour of the match is to signal only a clash
  if two constructors that are different are tried to be matched.
  For that reason we provide a facility for extracting the testfunctions
  from a HasCASL signature.
-}

getConstructors :: Assumps -> Map.Map Id (Set.Set TypeScheme)
getConstructors a = let constrs = Map.map (Set.filter isConstructor) a
                    in Map.map (Set.map opType) 
                       $ Map.filter (not . Set.null) constrs


termIsConstructor :: Assumps -> Term -> Bool
termIsConstructor a t = case toSConst t of
                          Nothing -> False
                          Just (SConst n ts) -> 
                              case Map.lookup n (getConstructors a) of
                                Just s -> Set.member ts s
                                _ -> False

-- | The noclash here depends only on each term seperately.
--   Only when the predicate on both terms evaluates to true a clash occurs.
noclashHeadInduced :: (Term -> Bool) -> Term -> Term -> Bool
noclashHeadInduced p t1 t2 = not (p t1) || not (p t2)

-- TODO: find out if we need to check for equality in the first case!
-- | The noclash here is induced only by the noclashHead function
noclashInduced :: (Term -> Term -> Bool) -> Term -> Term -> Bool
noclashInduced p (ApplTerm f1 _ _) (ApplTerm f2 _ _) = p f1 f2
noclashInduced _ _ _ = True

-- | The default noclash functions for the matching.
--   We assume that equality of terms is handled before.
defaultNoclashFromAssumps ::
    Assumps -> (Term -> Term -> Bool, Term -> Term -> Bool)
defaultNoclashFromAssumps a =
    let p = termIsConstructor a
        nch = noclashHeadInduced p
    in (nch, noclashInduced nch)
    

defaultmatch :: (Monad m) => Assumps -> Subst -> Set.Set SubstConst
             -> Term -> Term -> m (Subst, [(Term, Term)])
defaultmatch a s c = let (nch, nc) = defaultNoclashFromAssumps a in
                     match s c nch nc

{- |
  
* OVERVIEW OF THE ALGORITHM

Input: 
- map = constant->term mapping for constant definition expansion
- consts = set of constants to match, the others will be added as constraints
- noclash = a function taking two constants which produced a clash
            and returning whether or not this clash should be ignored and
            the corresponding term-pair should be added to the constraints
  actually we have two functions here:
    1. noclash-head: checks whether application-term heads produce a clash
    2. noclash: checks whether terms in general produce a clash.
                Only invoked after definition expansion.
- t1 = term pattern
- t2 = concrete term to be matched against the pattern


Output:
- s = a substitution containing the equalities which make the pattern and the term equal
- cstr = constraint list of equalities which have to be satisfied: in the case
         where a constant in t2 is encountered which cannot be expanded, but the corresponding pattern
         part is still not atomic, or where we get a clash between non-constructor terms

To support backtracking we should implement the output as a (lazy) list

-}
match :: (Monad m) => Subst -> Set.Set SubstConst -> (Term -> Term -> Bool)
      -> (Term -> Term -> Bool) -> Term -> Term -> m (Subst, [(Term, Term)])
match m consts noclashHead noclash t1 t2 =
    matchAux m consts noclashHead noclash (eps, []) (t1, t2)


matchAux :: (Monad m) => Subst -> Set.Set SubstConst -> (Term -> Term -> Bool)
         -> (Term -> Term -> Bool) -> (Subst, [(Term, Term)]) -> (Term, Term)
         -> m (Subst, [(Term, Term)])
matchAux m consts noclashHead noclash output@(sbst, ctrts) terms@(t1, t2) =
    case terms of
      -- handle the 'skip-cases' first
      (TypedTerm term _ _ _, _) -> match' term t2
      (_, TypedTerm term _ _ _) -> match' t1 term

      -- check for clash, handle constraints and definition expansion
      (ApplTerm f1 a1 _, _) ->
          case t2 of
            ApplTerm f2 a2 _ | f1 == f2 -> match' a1 a2
                             | noclashHead f1 f2 -> addLocalConstraint
            _ -> tryDefExpand

      (TupleTerm l _, _) -> 
          case t2 of
            TupleTerm l' _ | length l == length l' ->
                               foldM matchF output $ zip l l'
                           | otherwise -> tupleClash l l'
            _ -> tryDefExpand

      -- add the mapping v->t2 to output
      (QualVar v, _) -> addMapping v
      -- add the mapping (n,typ)->t2 to output
      (QualOp _ n typ _ _ _, _) -> addMapping (n,typ)

      -- all other terms are not expected and accepted here
      _ -> fail "matchAux: unhandled term"

      where matchF = matchAux m consts noclashHead noclash -- used for fold
            match' = curry $ matchF output
            addMapping k =
                let sc = toSC k in
                if Set.member sc consts then
                    case lookupContent sbst sc of
                      Just t' | t2 == t' -> return output
                              | otherwise ->
                                  fail $ concat [ "matchAux: Conflicting "
                                                , "substitution for ", show k]
                      _ -> return (addTerm sbst sc t2, ctrts)
                else addLocalConstraint
            addLocalConstraint | t1 == t2 = return output
                               | otherwise = return (sbst, (t1,t2):ctrts)
            -- The definition expansion application case
            -- (for ApplTerm and TupleTerm) is handled uniformly
            tryDefExpand = case defExpansion t2 of
                             Just t2' -> match' t1 t2'
                             _ | noclash t1 t2 -> addLocalConstraint
                               | otherwise -> clash


            defExpansion = lookupContent m
            clash = fail $ "matchAux: Clash for " ++ show (pretty (t1,t2))
            tupleClash l l' = fail $ "matchAux: Clash for tuples "
                              ++ show (pretty (l, l'))




-- new version of matcher with simpler interface
{- The rules of matching:

   f,g are functions
   c is a constant
   v is a variable
   t1, t2 are arbitrary terms
   "good" functions are the list-constructor, the solidworks datatype constructors and all other constructors.

   f != g

   1a. f(x_i) f(y_i) -> match x_i y_i,                  if f is a "good" function
                        AddConstraint f(x_i) = f(y_i),  otherwise

   1b. f(...) g(...) -> AddConstraint f(...) = g(...)

   2a. c t2 -> match t1 t2,           if c is defined by term t1
               AddConstraint c = t2,  otherwise

   2b. t1 c -> match t1 t2,           if c is defined by term t2
               AddConstraint t1 = c,  otherwise

   3. v t2 -> AddMatch v t2

-}
{- We need two classes:

   1. A class for lookup definitions and checking for good functions

   2. A class for storing the match (substitution plus constraints)
-}

class DefStore a where
    isGood :: a -> Term -> Bool
    getDefinition :: a -> Term -> Maybe Term

class Match a where
    addMatch :: a -> VarDecl -> Term -> a
    addConstraint :: a -> Term -> Term -> a


instance DefStore Env where
    isGood _ _ = True
    getDefinition = getOpDefinition

type MatchResult = (Subst, [(Term, Term)])

instance Match MatchResult where
    addMatch mr@(sb, ctrts) k t =
        let sc = toSC k
        in case lookupContent sb sc of
             Just t' | t == t' -> mr
                     | otherwise ->
                         error $ concat [ "addMatch: Conflicting "
                                        , "substitution for ", show (pretty k) ]
             _ -> (addTerm sb sc t, ctrts)

    addConstraint (sb, ctrts) t1 t2 = (sb, (t1, t2):ctrts)

newmatch :: (DefStore d, Match a) => d -> a -> Term -> Term -> Either String a
newmatch def mtch t1 t2 =
    case (t1, t2) of
      -- handle the 'skip-cases' first
      (TypedTerm term _ _ _, _) -> match' term t2
      (_, TypedTerm term _ _ _) -> match' t1 term

      -- check for clash, handle constraints and definition expansion
      (ApplTerm f1 a1 _, _) ->
          case t2 of
            ApplTerm f2 a2 _
                -- 1a1.
                | f1 == f2 && isGood def f1 -> match' a1 a2
                -- 1a2., 1b.
                | otherwise -> addLocalConstraint

            -- eventually 2b.
            _ -> tryDefExpand2

      (TupleTerm l _, _) -> 
          case t2 of
            TupleTerm l' _ | length l == length l' -> matchfold mtch $ zip l l'
                           | otherwise -> tupleClash
            -- eventually 2b.
            _ -> tryDefExpand2

      -- 3.: add the mapping v->t2 to output
      (QualVar v, _) -> addMapping v
      -- 2a.: follow the definition
      (QualOp _ _ _ _ _ _, _) -> tryDefExpand1

      -- all other terms are not expected and accepted here
      _ -> Left "newmatch: unhandled term"

      where match' = newmatch def mtch
            -- The definition expansion application case
            -- (for ApplTerm and TupleTerm) is handled uniformly
            tryDefExpand1 = case getDefinition def t1 of
                             Just t1' -> match' t1' t2
                             _ -> addLocalConstraint
            tryDefExpand2 = case getDefinition def t2 of
                             Just t2' -> match' t1 t2'
                             _ -> addLocalConstraint
            addLocalConstraint = Right $ addConstraint mtch t1 t2
            addMapping k = Right $ addMatch mtch k t2
            matchfold mtch' (x:l) = case uncurry (newmatch def mtch') x of
                                      Right mtch'' -> matchfold mtch'' l
                                      err -> err
            matchfold mtch' [] = Right mtch'
            clash = Left $ "newmatch: Clash for " ++ show (pretty (t1,t2))
            tupleClash = Left $ "newmatch: Clash for tuples "
                              ++ show (pretty (t1,t2))


startnewmatch :: Env -> Term -> Term -> Either String MatchResult
startnewmatch e t1 t2 = newmatch e (eps, []) t1 t2

------------------------- term tools -------------------------

getOpInfo :: Env -> Term -> Maybe OpInfo
getOpInfo e (QualOp _ (PolyId opid _ _) typ _ _ _) =
    case Map.lookup opid (assumps e) of
      Just soi ->
          let fs = Set.filter f soi
          in if Set.null fs then Nothing
             else Just $ Set.findMin fs
      _ -> Nothing
    where
      f oi = opType oi == typ
getOpInfo _ _ = Nothing

getOpDefinition :: Env -> Term -> Maybe Term
getOpDefinition e t =
    case fmap opDefn $ getOpInfo e t of
      Just (Definition _ t') -> Just t'
      _ -> Nothing

