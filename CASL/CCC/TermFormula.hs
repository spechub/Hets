{- |
Module      :  $Header$
Description :  auxiliary functions on terms and formulas
Copyright   :  (c) Mingyi Liu, Till Mossakowski, Uni Bremen 2004-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Auxiliary functions on terms and formulas
-}

module CASL.CCC.TermFormula where

import CASL.AS_Basic_CASL
import CASL.Fold
import CASL.Overload (leqF)
import CASL.Sign

import Common.Id (Range, GetRange (..))
import qualified Common.Lib.MapSet as MapSet

import Data.Function

-- | the sorted term is always ignored
unsortedTerm :: TERM f -> TERM f
unsortedTerm t = case t of
  Sorted_term t' _ _ -> unsortedTerm t'
  Cast t' _ _ -> unsortedTerm t'
  _ -> t

-- | the quantifier of term is always ignored
quanti :: FORMULA f -> FORMULA f
quanti f = case f of
  Quantification _ _ f' _ -> quanti f'
  _ -> f

-- | check whether it exist a (unique)existent quantification
isExQuanti :: FORMULA f -> Bool
isExQuanti f = case f of
  Quantification Universal _ f' _ -> isExQuanti f'
  Quantification {} -> True
  Relation f1 _ f2 _ -> isExQuanti f1 || isExQuanti f2
  Negation f' _ -> isExQuanti f'
  _ -> False

-- | check whether it contains a membership formula
isMembership :: FORMULA f -> Bool
isMembership f = case f of
  Quantification _ _ f' _ -> isMembership f'
  Junction _ fs _ -> any isMembership fs
  Negation f' _ -> isMembership f'
  Relation f1 _ f2 _ -> isMembership f1 || isMembership f2
  Membership {} -> True
  _ -> False

-- | check whether it contains a definedness formula
containDef :: FORMULA f -> Bool
containDef f = case f of
  Quantification _ _ f' _ -> containDef f'
  Junction _ fs _ -> any containDef fs
  Relation f1 _ f2 _ -> containDef f1 || containDef f2
  Negation f' _ -> containDef f'
  Definedness _ _ -> True
  _ -> False

-- | check whether it contains a negation
containNeg :: FORMULA f -> Bool
containNeg f = case f of
  Quantification _ _ f' _ -> containNeg f'
  Relation _ c f' _ | c /= Equivalence -> containNeg f'
  Relation f' Equivalence _ _ -> containNeg f'
  Negation _ _ -> True
  _ -> False

-- | check whether it is a Variable
isVar :: TERM t -> Bool
isVar t = case unsortedTerm t of
  Qual_var {} -> True
  _ -> False

-- | extract all variables of a term
varOfTerm :: Ord f => TERM f -> [TERM f]
varOfTerm t = case unsortedTerm t of
  Qual_var {} -> [t]
  Application _ ts _ -> concatMap varOfTerm ts
  _ -> []

-- | extract all arguments of a term
arguOfTerm :: TERM f -> [TERM f]
arguOfTerm t = case unsortedTerm t of
  Qual_var {} -> [t]
  Application _ ts _ -> ts
  _ -> []

-- | create the obligation of subsort
infoSubsort :: [SORT] -> FORMULA f -> [FORMULA f]
infoSubsort sts f = case f of
  Quantification Universal v
    (Relation (Membership _ s _) Equivalence f1 _) r ->
      [Quantification Existential v f1 r | notElem s sts]
  _ -> []

-- | extract the leading symbol from a formula
leadingSym :: GetRange f => FORMULA f -> Maybe (Either OP_SYMB PRED_SYMB)
leadingSym = fmap extractLeadingSymb . leadingTermPredication

-- | extract the leading symbol with the range from a formula
leadingSymPos :: GetRange f => FORMULA f
  -> (Maybe (Either (TERM f) (FORMULA f)), Range)
leadingSymPos f = leading (f, False, False, False) where
  -- three booleans to indicate inside implication, equivalence or negation
  leadTerm t q = case unsortedTerm t of
    a@(Application _ _ p) -> (Just (Left a), p)
    _ -> (Nothing, q)
  leading (f1, b1, b2, b3) = case (quanti f1, b1, b2, b3) of
    (Negation f' _, _, _, False) ->
        leading (f', b1, b2, True)
    (Relation _ c f' _, False, False, False)
        | c /= Equivalence ->
        leading (f', True, False, False)
    (Relation f' Equivalence _ _, _, False, False) ->
        leading (f', b1, True, False)
    (Definedness t q, _, _, _) -> leadTerm t q
    (pr@(Predication _ _ p), _, _, _) ->
        (Just (Right pr), p)
    (Equation t _ _ q, _, False, False) -> leadTerm t q
    _ -> (Nothing, getRange f1)

-- | extract the leading term or predication from a formula
leadingTermPredication :: GetRange f => FORMULA f
  -> Maybe (Either (TERM f) (FORMULA f))
leadingTermPredication = fst . leadingSymPos

-- | extract the leading symbol from a term or a formula
extractLeadingSymb :: Either (TERM f) (FORMULA f) -> Either OP_SYMB PRED_SYMB
extractLeadingSymb lead = case lead of
  Left (Application os _ _) -> Left os
  Right (Predication p _ _) -> Right p
  _ -> error "CASL.CCC.TermFormula<extractLeadingSymb>"

-- | replaces variables by terms in a term or formula
substRec :: Eq f => [(TERM f, TERM f)] -> Record f (FORMULA f) (TERM f)
substRec subs = (mapRecord id)
   { foldQual_var = \ t _ _ _ -> subst subs t } where
  subst l tt = case l of
    [] -> tt
    (n, v) : r -> if tt == v then n else subst r tt

substitute :: Eq f => [(TERM f, TERM f)] -> TERM f -> TERM f
substitute = foldTerm . substRec

substiF :: Eq f => [(TERM f, TERM f)] -> FORMULA f -> FORMULA f
substiF = foldFormula . substRec

-- | check whether two terms are the terms of same application symbol
sameOpsApp :: Sign f e -> TERM f -> TERM f -> Bool
sameOpsApp sig app1 app2 = case (unsortedTerm app1, unsortedTerm app2) of
  (Application (Qual_op_name ops1 t1 _) _ _
    , Application (Qual_op_name ops2 t2 _) _ _)
    -> ops1 == ops2 && on (leqF sig) toOpType t1 t2
  _ -> False

-- | get or create a variable declaration for a formula
varDeclOfF :: Ord f => FORMULA f -> [VAR_DECL]
varDeclOfF = let
  qualVarToDecl t = case t of
    Qual_var v s r -> MapSet.insert (s, r) v MapSet.empty
    _ -> MapSet.empty
  varDeclToDecl (Var_decl vs s r) = MapSet.fromList [((s, r), vs)]
  unions = foldr MapSet.union MapSet.empty
  termMap = unions . map qualVarToDecl . varOfTerm
  declMap f = case f of
    Quantification _ vds _ _ -> unions $ map varDeclToDecl vds
    Junction _ fs _ -> unions $ map declMap fs
    Relation f1 _ f2 _ -> on MapSet.union declMap f1 f2
    Negation f' _ -> declMap f'
    Predication _ ts _ -> unions $ map termMap ts
    Definedness t _ -> termMap t
    Equation t1 _ t2 _ -> on MapSet.union termMap t1 t2
    _ -> MapSet.empty
  in map (\ ((s, r), vs) -> Var_decl vs s r) . MapSet.toList . declMap
