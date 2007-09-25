{- |
Module      :  $Header$
Description :  mark certain Isabelle sentenes for the simplifier
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

try to recognize formulas for the simplifier
-}

module Isabelle.MarkSimp (markSimp) where

import Isabelle.IsaSign
import Isabelle.IsaConsts

import Common.AS_Annotation

markSimp :: Named Sentence -> Named Sentence
markSimp s = if isDef s then s else
             mapNamed (markSimpSen isSimpRuleSen) s

markSimpSen :: (Sentence -> Bool) -> Sentence -> Sentence
markSimpSen f s = case s of
                  Sentence {} -> s {isSimp = f s}
                  _ -> s

isSimpRuleSen :: Sentence -> Bool
isSimpRuleSen sen = case sen of
    RecDef {} -> False
    _ -> isSimpRule $ senTerm sen

-- | test whether a formula should be put into the simpset
isSimpRule :: Term -> Bool
-- only universal quantifications
isSimpRule trm = case trm of
    App (Const q _) arg@Abs{} _
        | new q == exS || new q == ex1S -> False
        | new q == allS  -> isSimpRule (termId arg)
    App (App (Const q _) a1 _) a2 _
        | new q == eq -> sizeOfTerm a1 > sizeOfTerm a2
        | new q == impl -> sizeOfTerm a1 < sizeOfTerm a2
    _ -> True

sizeOfTerm :: Term -> Int
sizeOfTerm trm = case trm of
    Abs { termId = t } -> sizeOfTerm t + 1
    App { funId = t1, argId = t2 } -> sizeOfTerm t1 + sizeOfTerm t2
    If { ifId = t1, thenId = t2, elseId = t3 } ->
        sizeOfTerm t1 + max (sizeOfTerm t2) (sizeOfTerm t3)
    Case { termId = t1, caseSubst = cs } ->
        sizeOfTerm t1 + foldr max 0 (map (sizeOfTerm . snd) cs)
    Let { letSubst = es, inId = t } ->
        sizeOfTerm t + sum (map (sizeOfTerm . snd) es)
    IsaEq { firstTerm = t1, secondTerm = t2 } ->
        sizeOfTerm t1 + sizeOfTerm t2 + 1
    Tuplex ts _ -> sum $ map sizeOfTerm ts
    _ -> 1
