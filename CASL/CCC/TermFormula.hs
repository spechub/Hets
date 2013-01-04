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
import CASL.Overload (leqF, leqSort)
import CASL.Sign (OpMap, Sign, toOP_TYPE, toOpType)

import Common.Id (Range, GetRange (..), nullRange)
import Common.Utils (nubOrd)
import qualified Common.Lib.MapSet as MapSet

import qualified Data.Set as Set

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
isExQuanti f =
    case f of
      Quantification Universal _ f' _ -> isExQuanti f'
      Quantification {} -> True
      Relation f1 _ f2 _ -> isExQuanti f1 || isExQuanti f2
      Negation f' _ -> isExQuanti f'
      _ -> False

-- | get the constraint from a sort generated axiom
constraintOfAxiom :: FORMULA f -> [Constraint]
constraintOfAxiom f =
    case f of
      Sort_gen_ax constrs _ -> constrs
      _ -> []

-- | check whether it contains a membership formula
isMembership :: FORMULA f -> Bool
isMembership f =
  case f of
    Quantification _ _ f' _ -> isMembership f'
    Junction _ fs _ -> any isMembership fs
    Negation f' _ -> isMembership f'
    Relation f1 _ f2 _ -> isMembership f1 || isMembership f2
    Membership {} -> True
    _ -> False

-- | check whether a sort is free generated
isFreeGenSort :: SORT -> [FORMULA f] -> Maybe Bool
isFreeGenSort _ [] = Nothing
isFreeGenSort s (f : fs) =
  case f of
    Sort_gen_ax csts isFree | any ((== s) . newSort) csts -> Just isFree
    _ -> isFreeGenSort s fs

-- | check whether it is the domain of a partial function
isDomain :: FORMULA f -> Bool
isDomain f = case quanti f of
    Relation (Definedness _ _) Equivalence f' _ -> not (containDef f')
    Definedness _ _ -> True
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

-- | check whether it contains a definedness formula in correct form
correctDef :: FORMULA f -> Bool
correctDef f = case quanti f of
             Relation _ c (Definedness _ _) _ | c /= Equivalence -> False
             Relation (Definedness _ _) c _ _ | c /= Equivalence -> True
             Relation (Definedness _ _) Equivalence f' _ -> not (containDef f')
             Negation (Definedness _ _) _ -> True
             Definedness _ _ -> True
             _ -> False

-- | extract all partial function symbols, their domains are defined
domainOpSymbs :: [FORMULA f] -> [OP_SYMB]
domainOpSymbs = concatMap domOpS
  where domOpS f = case quanti f of
          Relation (Definedness t _) Equivalence _ _ -> [opSymbOfTerm t]
          _ -> []

-- | check whether a formula gives the domain of a partial function
domainOs :: FORMULA f -> OP_SYMB -> Bool
domainOs f os = case quanti f of
    Relation (Definedness t _) Equivalence _ _ -> opSymbOfTerm t == os
    _ -> False

-- | extract the domain-list of partial functions
domainList :: [FORMULA f] -> [(TERM f, FORMULA f)]
domainList = concatMap dm
  where dm f = case quanti f of
                 Relation (Definedness t _) Equivalence f' _ -> [(t, f')]
                 _ -> []

-- | check whether it is a Variable
isVar :: TERM t -> Bool
isVar t = case unsortedTerm t of
            Qual_var {} -> True
            _ -> False

-- | extract the operation symbol from a term
opSymbOfTerm :: TERM f -> OP_SYMB
opSymbOfTerm t = case unsortedTerm t of
                   Application os _ _ -> os
                   Conditional t' _ _ _ -> opSymbOfTerm t'
                   _ -> error "CASL.CCC.TermFormula.<opSymbOfTerm>"

-- | extract all variables of a term
varOfTerm :: Ord f => TERM f -> [TERM f]
varOfTerm t = case unsortedTerm t of
                Qual_var {} -> [t]
                Application _ ts _ -> nubOrd $ concatMap varOfTerm ts
                _ -> []

-- | extract all arguments of a term
arguOfTerm :: TERM f -> [TERM f]
arguOfTerm t = case unsortedTerm t of
                 Qual_var {} -> [t]
                 Application _ ts _ -> ts
                 _ -> []

-- | extract all arguments of a predication
arguOfPred :: FORMULA f -> [TERM f]
arguOfPred f = case quanti f of
                 Negation f1 _ -> arguOfPred f1
                 Predication _ ts _ -> ts
                 _ -> []

-- | extract the predication symbols from a axiom
predSymbsOfAxiom :: FORMULA f -> [PRED_SYMB]
predSymbsOfAxiom f = case f of
      Quantification _ _ f' _ -> predSymbsOfAxiom f'
      Junction _ fs _ -> concatMap predSymbsOfAxiom fs
      Relation f1 _ f2 _ -> predSymbsOfAxiom f1 ++ predSymbsOfAxiom f2
      Negation f' _ -> predSymbsOfAxiom f'
      Predication p_s _ _ -> [p_s]
      _ -> []

-- | check whether it is a partial axiom
partialAxiom :: GetRange f => FORMULA f -> Bool
partialAxiom f = case opTypAxiom f of
      Just False -> True
      _ -> False

-- | create the obligation of subsort
infoSubsort :: [SORT] -> FORMULA f -> [FORMULA f]
infoSubsort sts f =
    case f of
      Quantification Universal v
           (Relation (Membership _ s _) Equivalence f1 _) _ ->
           [Quantification Existential v f1 nullRange | notElem s sts]
      _ -> []

-- | extract the leading symbol from a formula
leadingSym :: GetRange f => FORMULA f -> Maybe (Either OP_SYMB PRED_SYMB)
leadingSym = fmap extractLeadingSymb . leadingTermPredication

-- | extract the leading symbol with the range from a formula
leadingSymPos :: GetRange f => FORMULA f
  -> (Maybe (Either (TERM f) (FORMULA f)), Range)
leadingSymPos f = leading (f, False, False, False) where
  -- three booleans to indicate inside implication, equivalence or negation
  leading (f1, b1, b2, b3) = case (quanti f1, b1, b2, b3) of
                           (Quantification _ _ f' _, _, _, _) ->
                               leading (f', b1, b2, b3)
                           (Negation f' _, _, _, False) ->
                               leading (f', b1, b2, True)
                           (Relation _ c f' _, False, False, False)
                               | c /= Equivalence ->
                               leading (f', True, False, False)
                           (Relation f' Equivalence _ _, _, False, False) ->
                               leading (f', b1, True, False)
                           (Definedness t _, _, _, _) ->
                               case unsortedTerm t of
                                 a@(Application _ _ p) -> (Just (Left a), p)
                                 _ -> (Nothing, getRange f1)
                           (pr@(Predication _ _ p), _, _, _) ->
                               (Just (Right pr), p)
                           (Equation t _ _ _, _, False, False) ->
                               case unsortedTerm t of
                                 a@(Application _ _ p) -> (Just (Left a), p)
                                 _ -> (Nothing, getRange f1)
                           _ -> (Nothing, getRange f1)

-- | extract the leading term or predication from a formula
leadingTermPredication :: GetRange f => FORMULA f
  -> Maybe (Either (TERM f) (FORMULA f))
leadingTermPredication = fst . leadingSymPos

-- | extract the leading symbol from a term or a formula
extractLeadingSymb :: Either (TERM f) (FORMULA f) -> Either OP_SYMB PRED_SYMB
extractLeadingSymb lead =
    case lead of
      Left (Application os _ _) -> Left os
      Right (Predication p _ _) -> Right p
      _ -> error "CASL.CCC.TermFormula<extractLeadingSymb>"

{- | leadingTerm is total operation : Just True,
leadingTerm is partial operation : Just False,
others : Nothing. -}
opTypAxiom :: GetRange f => FORMULA f -> Maybe Bool
opTypAxiom f = case leadingSym f of
    Just (Left t) -> case t of
      Qual_op_name _ (Op_type k _ _ _) _ -> Just $ k == Total
      _ -> Nothing
    _ -> Nothing

-- | extract the overloaded constructors
constructorOverload :: Sign f e -> OpMap -> [OP_SYMB] -> [OP_SYMB]
constructorOverload s opm = concatMap cons_Overload
    where cons_Overload o = case o of
                Op_name _ -> [o]
                Qual_op_name on1 ot _ ->
                    concatMap (cons on1 ot) $ Set.toList $ MapSet.lookup on1 opm
          cons on opt1 opt2 = [Qual_op_name on (toOP_TYPE opt2) nullRange |
                               leqF s (toOpType opt1) opt2]

-- | check whether the operation symbol is a constructor
isCons :: Sign f e -> [OP_SYMB] -> OP_SYMB -> Bool
isCons s cons os = any (is_Cons os) cons
    where is_Cons (Op_name _) _ = False
          is_Cons _ (Op_name _) = False
          is_Cons (Qual_op_name on1 (Op_type _ s1 r1 _) _)
                      (Qual_op_name on2 (Op_type _ s2 r2 _) _) =
            -- we expect the symbol to allow more values than the constructor
            on1 == on2 && leqSort s r2 r1
            && length s1 == length s2
            && and (zipWith (leqSort s) s2 s1)
            -- maybe leqF or just equality would be fine, too

-- | replaces variables by terms in a term
substitute :: Eq f => [(TERM f, TERM f)] -> TERM f -> TERM f
substitute subs t = case t of
    t'@(Qual_var {}) ->
      subst subs t'
    Application os ts r ->
      Application os (map (substitute subs) ts) r
    Sorted_term te s r ->
      Sorted_term (substitute subs te) s r
    Cast te s r ->
      Cast (substitute subs te) s r
    Conditional t1 f t2 r ->
      Conditional (substitute subs t1) (substiF subs f) (substitute subs t2) r
    Mixfix_term ts ->
      Mixfix_term (map (substitute subs) ts)
    Mixfix_parenthesized ts r ->
      Mixfix_parenthesized (map (substitute subs) ts) r
    Mixfix_bracketed ts r ->
      Mixfix_bracketed (map (substitute subs) ts) r
    Mixfix_braced ts r ->
      Mixfix_braced (map (substitute subs) ts) r
    _ -> t
  where subst [] tt = tt
        subst (x : xs) tt = if tt == snd x then fst x
                          else subst xs tt

-- | replaces variables by terms in a formula
substiF :: Eq f => [(TERM f, TERM f)] -> FORMULA f -> FORMULA f
substiF subs f = case f of
    Quantification q v f' r -> Quantification q v (substiF subs f') r
    Junction j fs r -> Junction j (map (substiF subs) fs) r
    Relation f1 c f2 r -> Relation (substiF subs f1) c (substiF subs f2) r
    Negation f' r -> Negation (substiF subs f') r
    Predication ps ts r -> Predication ps (map (substitute subs) ts) r
    Equation t1 e t2 r -> Equation (substitute subs t1) e (substitute subs t2) r
    Membership t s r -> Membership (substitute subs t) s r
    Mixfix_formula t -> Mixfix_formula (substitute subs t)
    _ -> f

-- | check whether two terms are the terms of same application symbol
sameOpsApp :: TERM f -> TERM f -> Bool
sameOpsApp app1 app2 = case unsortedTerm app1 of
                          Application ops1 _ _ ->
                              case unsortedTerm app2 of
                                Application ops2 _ _ -> ops1 == ops2
                                _ -> False
                          _ -> False

-- | get the axiom range of a term
axiomRangeforTerm :: (GetRange f, Eq f) => [FORMULA f] -> TERM f -> Range
axiomRangeforTerm [] _ = nullRange
axiomRangeforTerm fs t =
    case leadingTermPredication (head fs) of
      Just (Left tt) -> if tt == t
                          then getRange $ quanti $ head fs
                          else axiomRangeforTerm (tail fs) t
      _ -> axiomRangeforTerm (tail fs) t

-- | get the sort of a variable declaration
sortOfVarD :: VAR_DECL -> SORT
sortOfVarD (Var_decl _ s _) = s

-- | get or create a variable declaration for a formula
varDeclOfF :: Ord f => FORMULA f -> [VAR_DECL]
varDeclOfF f =
    case f of
      Quantification _ vds _ _ -> vds
      Junction _ fs _ -> concatVD $ nubOrd $ concatMap varDeclOfF fs
      Relation f1 _ f2 _ -> concatVD $ nubOrd $ varDeclOfF f1 ++
                                  varDeclOfF f2
      Negation f' _ -> varDeclOfF f'
      Predication _ ts _ -> varD $ nubOrd $ concatMap varOfTerm ts
      Definedness t _ -> varD $ varOfTerm t
      Equation t1 _ t2 _ -> varD $ nubOrd $ varOfTerm t1 ++ varOfTerm t2
      _ -> []
  where varD [] = []
        varD vars@(v : vs) =
            case v of
              Qual_var _ s r ->
                Var_decl (nubOrd $ map varOfV $
                           filter (\ v' -> sortOfV v' == s) vars) s r :
                varD (filter (\ v' -> sortOfV v' /= s) vs)
              _ -> error "CASL.CCC.TermFormula<varD>"
        concatVD [] = []
        concatVD vd@(Var_decl _ s r : vds) =
            Var_decl (nubOrd $ concatMap vOfVD $
                       filter (\ v' -> sortOfVarD v' == s) vd) s r :
            concatVD (filter (\ v' -> sortOfVarD v' /= s) vds)
        vOfVD (Var_decl vs _ _) = vs
        sortOfV (Qual_var _ s _) = s
        sortOfV _ = error "CASL.CCC.TermFormula<sortOfV>"
        varOfV (Qual_var v _ _) = v
        varOfV _ = error "CASL.CCC.TermFormula<varOfV>"
