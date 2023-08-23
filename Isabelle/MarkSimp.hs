{- |
Module      :  ./Isabelle/MarkSimp.hs
Description :  mark certain Isabelle sentenes for the simplifier
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

try to recognize formulas for the simplifier
-}

module Isabelle.MarkSimp (markSimp, markThSimp) where

import Isabelle.IsaSign
import Isabelle.IsaConsts

import Common.AS_Annotation

import Data.List (isPrefixOf)

markSimp :: Named Sentence -> Named Sentence
markSimp = markSimpAux True

markThSimp :: Named Sentence -> Named Sentence
markThSimp = markSimpAux False

markSimpAux :: Bool -> Named Sentence -> Named Sentence
markSimpAux isAx s = let
  prefixIsin = any (flip isPrefixOf $ senAttr s)
  hasSimp b = simpAnno s == Just b
  in if isDef s || hasSimp False || prefixIsin excludePrefixes
    then s else mapNamed (markSimpSen $ \ ns -> hasSimp True
      || isAx && isSimpRuleSen ns || prefixIsin includePrefixes) s

excludePrefixes :: [String]
excludePrefixes = [ "ga_predicate_monotonicity"
                  , "ga_function_monotonicity"
                  , "ga_transitive"]

includePrefixes :: [String]
includePrefixes =
    [ "ga_comm_"
    , "ga_assoc_"
    , "ga_left_comm_"]

markSimpSen :: (Sentence -> Bool) -> Sentence -> Sentence
markSimpSen f s = case s of
                  Sentence {} -> s {isSimp = f s}
                  _ -> s

isSimpRuleSen :: Sentence -> Bool
isSimpRuleSen sen = case sen of
    Sentence {metaTerm = Term t} -> isCondEq t
    _ -> False

isSimplAppl :: Term -> Bool
isSimplAppl trm = case trm of
    Free {} -> True
    Const q _ -> notElem (new q)
      [allS, exS, ex1S, eq, impl, disj, conj, cNot]
    App f a _ -> isSimplAppl f && isSimplAppl a
    Tuplex ts _ -> all isSimplAppl ts
    _ -> False

isEqOrSimplAppl :: Term -> Bool
isEqOrSimplAppl trm = case trm of
    App (App (Const q _) a1 _) a2 _ | new q == eq ->
        isSimplAppl a1 && isSimplAppl a2 && sizeOfTerm a1 > sizeOfTerm a2
    _ -> isSimplAppl trm

isEqOrNeg :: Term -> Bool
isEqOrNeg trm = case trm of
    App (Const q _) arg _ | new q == cNot -> isEqOrNeg arg
    _ -> isEqOrSimplAppl trm

isCondEq :: Term -> Bool
isCondEq trm = case trm of
    App (Const q _) arg@Abs {} _ | new q == allS -> isCondEq (termId arg)
    App (App (Const q _) a1 _) a2 _
        | new q == impl -> isEqOrNeg a1 && isCondEq a2
        | new q == conj -> isCondEq a1 && isCondEq a2
    _ -> isEqOrNeg trm

sizeOfTerm :: Term -> Int
sizeOfTerm trm = case trm of
    Abs { termId = t } -> sizeOfTerm t + 1
    App { funId = t1, argId = t2 } -> sizeOfTerm t1 + sizeOfTerm t2
    If { ifId = t1, thenId = t2, elseId = t3 } ->
        sizeOfTerm t1 + max (sizeOfTerm t2) (sizeOfTerm t3)
    Case { termId = t1, caseSubst = cs } ->
        sizeOfTerm t1 + foldr (max . sizeOfTerm . snd) 0 cs
    Let { letSubst = es, inId = t } ->
        sizeOfTerm t + sum (map (sizeOfTerm . snd) es)
    IsaEq { firstTerm = t1, secondTerm = t2 } ->
        sizeOfTerm t1 + sizeOfTerm t2 + 1
    Tuplex ts _ -> sum $ map sizeOfTerm ts
    _ -> 1
