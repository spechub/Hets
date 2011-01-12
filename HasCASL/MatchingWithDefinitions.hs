{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  matching of terms modulo definition expansion
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  non-portable (see extensions)

Matching of terms modulo constant definition expansion and constraints
-}

module HasCASL.MatchingWithDefinitions where

import HasCASL.Subst
import HasCASL.PrintSubst

import HasCASL.As
import HasCASL.Le
import HasCASL.SimplifyTerm
import HasCASL.PrintAs ()

import Common.Id
import Common.ConvertGlobalAnnos()
import Common.Doc
import Common.DocUtils

import qualified Data.Map as Map
import qualified Data.Set as Set

{- New version of matcher with simpler interface.
   
   The rules of matching:

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
               AddMatch c t2,         if c is mapable
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
    isMapable :: a -> (Id, TypeScheme) -> Bool
    getDefinition :: a -> (Id, TypeScheme) -> Maybe Term
    getEnv :: a -> Env

class Match a where
    addMatch :: a -> SubstConst -> Term -> a
    addConstraint :: a -> Term -> Term -> a
    logMsg :: a -> String -> IO ()


newtype DefinitionStore = DefinitionStore (Env, Set.Set Symbol)

initialDefStore :: Env -> Set.Set Symbol -> DefinitionStore
initialDefStore e syms = DefinitionStore (e, syms)

instance DefStore DefinitionStore where
    isGood _ _ = True
    isMapable (DefinitionStore (e, syms)) (opid, typ) =
        Set.member (idToOpSymbol e opid typ) syms
    getDefinition (DefinitionStore (e, _)) = getOpDefinition e
    getEnv (DefinitionStore (e, _)) = e

newtype MatchResult = MatchResult (Subst, [(Term, Term)]) deriving Show

getMatchResult :: MatchResult -> (Subst, [(Term, Term)])
getMatchResult (MatchResult x) = x

emptyMatchResult :: MatchResult
emptyMatchResult = MatchResult (emptySubstitution, [])

instance PrettyInEnv MatchResult where
    prettyInEnv e (MatchResult (sb, ctrts)) =
        text "Match"
                 <> vcat [ text "result", prettyInEnv e sb
                         , text "Constraints", prettyTermMapping e ctrts ]


instance Match MatchResult where
    addMatch mr@(MatchResult (sb, ctrts)) sc t =
        case lookupContent sb sc of
          -- TODO: eventually add conflicting subst as constraint
          --  (the terms could be semantically equal)
             Just t' | t == t' -> mr
                     | otherwise ->
                         error $ concat [ "addMatch: Conflicting "
                                        , "substitution for ", show sc ]
             _ -> MatchResult (addTerm sb sc t, ctrts)

    addConstraint (MatchResult (sb, ctrts)) t1 t2 = MatchResult (sb, (t1, t2):ctrts)

    logMsg _ _ = return () -- appendFile "/tmp/matcher.out" . (++"\n")

match :: (DefStore d, Match a) => d -> a -> Term -> Term -> IO (Either String a)
match def mtch t1 t2 =
    case (t1, t2) of
      -- handle the 'skip-cases' first
      (TypedTerm term _ _ _, _) -> match' term t2 -- logg "typed1" $ match' term t2
      (_, TypedTerm term _ _ _) -> match' t1 term -- logg "typed2" $ match' t1 term

      -- check for clash, handle constraints and definition expansion
      (ApplTerm f1 a1 _, _) ->
          case t2 of
            ApplTerm f2 a2 _
                -- 1a1.
                | f1 == f2 && isGood def f1 -> logg msg1a1 $ match' a1 a2
                -- 1a2., 1b.
                | otherwise -> logg msg1a21b addLocalConstraint

            -- eventually 2b.
            _ -> logg msg2b $ tryDefExpand2

      (TupleTerm l _, _) -> 
          case t2 of
            TupleTerm l' _ | length l == length l' ->
                               logg msg1aT $ matchfold mtch $ zip l l'
                           | otherwise ->
                               logg "tclash" $ tupleClash
            -- eventually 2b.
            _ -> logg msg2bT $ tryDefExpand2

      -- 3.: add the mapping v->t2 to output
      (QualVar v, _) -> logg "mapped" $ addMapping v
      -- 2a.: follow the definition of pattern
      (QualOp _ (PolyId opid _ _) typ _ _ _, _) ->
          logg msg2a $ tryDefExpand1 (opid, typ)

      -- all other terms are not expected and accepted here
      _ -> return $ Left "match: unhandled term"

      where match' = match def mtch
            -- The definition expansion application case
            -- (for ApplTerm and TupleTerm) is handled uniformly
            tryDefExpand1 oi = case getTermDef t1 of
                                 Just t1' -> match' t1' t2
                                 _ | isMapable def oi -> addMapping oi
                                   | otherwise -> addLocalConstraint

            tryDefExpand2 = case getTermDef t2 of
                             Just t2' -> match' t1 t2'
                             _ -> addLocalConstraint

            getTermDef t = getTermOp t >>= getDefinition def
            addLocalConstraint
                -- Do not add constraints for equal terms
                | t1 == t2 = return $ Right mtch
                | otherwise = return $ Right $ addConstraint mtch t1 t2
            addMapping t = return $ Right $ addMatch mtch (toSC t) t2
            matchfold mtch' (x:l) = do
                    res <- uncurry (match def mtch') x
                    case res of
                      Right mtch'' -> matchfold mtch'' l
                      err -> return $ err
            matchfold mtch' [] = return $ Right mtch'
            --clash = return $ Left $ "match: Clash for " ++ show (pretty (t1,t2))
            tupleClash = return $ Left $ "match: Clash for tuples "
                         ++ show (pretty (t1,t2))

            -- Logging stuff
            logg s a = do
                    let e = getEnv def
                    logMsg mtch $ show $ useGlobalAnnos (globAnnos e)
                               $ text "Log" <+> text s
                               $++$ text "t1:" $+$ pretty (simplifyTerm e t1) $++$ text "t2:"
                               $+$ pretty (simplifyTerm e t2) $++$ text "==============="
                    a
            msg1a1 = "1a1: good same function"
            msg1a21b = "1a2, 1b: not good or not same function"
            msg1aT = "1aT: tuple: same tuple"
            msg2bT = "2bT:"
            msg2a = "2a: pattern constant"
            msg2b = "2b: term constant"


------------------------- term tools -------------------------

getTermOp :: Term -> Maybe (Id, TypeScheme)
getTermOp (QualOp _ (PolyId opid _ _) typ _ _ _) = Just (opid, typ)
getTermOp _ = Nothing

getOpInfo :: Env -> (Id, TypeScheme) -> Maybe OpInfo
getOpInfo e (opid, typ) =
    case Map.lookup opid (assumps e) of
      Just soi ->
          let fs = Set.filter f soi
          in if Set.null fs then Nothing
             else Just $ Set.findMin fs
      _ -> Nothing
    where
      f oi = opType oi == typ

getOpDefinition :: Env -> (Id, TypeScheme) -> Maybe Term
getOpDefinition e t =
    case fmap opDefn $ getOpInfo e t of
      Just (Definition _ t') -> Just t'
      _ -> Nothing
