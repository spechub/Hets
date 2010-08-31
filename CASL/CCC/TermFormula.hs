{- |
Module      :  $Header$
Description :  auxiliary functions on terms and formulas
Copyright   :  (c) Mingyi Liu and Till Mossakowski and Uni Bremen 2004-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  xinga@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Auxiliary functions on terms and formulas
-}

module CASL.CCC.TermFormula where

import CASL.AS_Basic_CASL
import CASL.Overload(leqF)
import CASL.Sign(OpMap, Sign(sortRel), toOP_TYPE, toOpType)

import Common.Id(Token(tokStr), Id(Id), Range, GetRange(..), nullRange)
import Common.Utils(nubOrd)
import qualified Common.Lib.Rel as Rel

import Control.Monad(liftM)
import qualified Data.Map as Map
import qualified Data.Set as Set

-- | the sorted term is always ignored
term :: TERM f -> TERM f
term t = case t of
           Sorted_term t' _ _ -> term t'
           _                  -> t


-- | the quantifier of term is always ignored
quanti :: FORMULA f -> FORMULA f
quanti f = case f of
             Quantification _ _ f' _ -> quanti f'
             _                       -> f


-- | check whether it exist a (unique)existent quantification
isExQuanti :: FORMULA f -> Bool
isExQuanti f =
    case f of
      Quantification Existential _ _ _        -> True
      Quantification Unique_existential _ _ _ -> True
      Quantification _ _ f' _                 -> isExQuanti f'
      Implication f1 f2 _ _                   -> isExQuanti f1 || isExQuanti f2
      Equivalence f1 f2 _                     -> isExQuanti f1 || isExQuanti f2
      Negation f' _                           -> isExQuanti f'
      _                                       -> False


-- | get the constraint from a sort generated axiom
constraintOfAxiom :: FORMULA f -> [Constraint]
constraintOfAxiom f =
    case f of
      Sort_gen_ax constrs _ -> constrs
      _                     -> []


-- | determine whether a formula is a sort generation constraint
isSortGen :: FORMULA a -> Bool
isSortGen (Sort_gen_ax _ _) = True
isSortGen _                 = False


-- | check whether it contains a membership formula
isMembership :: FORMULA f -> Bool
isMembership f =
  case f of
    Quantification _ _ f' _ -> isMembership f'
    Conjunction fs _        -> any isMembership fs
    Disjunction fs _        -> any isMembership fs
    Negation f' _           -> isMembership f'
    Implication f1 f2 _ _   -> isMembership f1 || isMembership f2
    Equivalence f1 f2 _     -> isMembership f1 || isMembership f2
    Membership _ _ _        -> True
    _                       -> False


-- | check whether a sort is free generated
isFreeGenSort :: SORT -> [FORMULA f] -> Maybe Bool
isFreeGenSort _ [] = Nothing
isFreeGenSort s (f:fs) =
  case f of
    Sort_gen_ax csts isFree | any ((== s) . newSort) csts -> Just isFree
    _ -> isFreeGenSort s fs


-- | check whether it is the domain of a partial function
isDomain :: FORMULA f -> Bool
isDomain f = case (quanti f) of
               Equivalence (Definedness _ _) f' _ -> not (containDef f')
               Definedness _ _                    -> True
               _                                  -> False


-- | check whether it contains a definedness formula
containDef :: FORMULA f -> Bool
containDef f = case f of
             Quantification _ _ f' _ -> containDef f'
             Conjunction fs _        -> any containDef fs
             Disjunction fs _        -> any containDef fs
             Implication f1 f2 _ _   -> containDef f1 || containDef f2
             Equivalence f1 f2 _     -> containDef f1 || containDef f2
             Negation f' _           -> containDef f'
             Definedness _ _         -> True
             _                       -> False


-- | check whether it contains a negation
containNeg :: FORMULA f -> Bool
containNeg f = case f of
                 Quantification _ _ f' _ -> containNeg f'
                 Implication _ f' _ _    -> containNeg f'
                 Equivalence f' _ _      -> containNeg f'
                 Negation _ _            -> True
                 _                       -> False


-- | check whether it contains a definedness formula in correct form
correctDef :: FORMULA f -> Bool
correctDef f = case (quanti f) of
             Implication _ (Definedness _ _) _ _ -> False
             Implication (Definedness _ _) _ _ _ -> True
             Equivalence (Definedness _ _) f' _  -> not (containDef f')
             Negation (Definedness _ _) _        -> True
             Definedness _ _                     -> True
             _                                   -> False


-- | extract all partial function symbols, their domains are defined
domainOpSymbs :: [FORMULA f] -> [OP_SYMB]
domainOpSymbs fs = concatMap domOpS fs
  where domOpS f = case (quanti f) of
                     Equivalence (Definedness t _) _ _ -> [opSymbOfTerm t]
                     _                                 -> []


-- | check whether a formula gives the domain of a partial function
domainOs :: FORMULA f -> OP_SYMB -> Bool
domainOs f os = case (quanti f) of
                   Equivalence (Definedness t _) _ _ -> opSymbOfTerm t == os
                   _                                 -> False


-- | extract the domain-list of partial functions
domainList :: [FORMULA f] -> [(TERM f,FORMULA f)]
domainList fs = concatMap dm fs
  where dm f = case (quanti f) of
                 Equivalence (Definedness t _) f' _ -> [(t,f')]
                 _                                  -> []


-- | check whether it is a implication
-- | Function seems to be unused.
{-isImpli :: FORMULA f -> Bool
isImpli f = case (quanti f) of
               Quantification _ _ f' _ -> isImpliEquiv f'
               Implication _ _ _ _ -> True
               Negation f' _ -> isImpliEquiv f'
               _ -> False-}


-- | check whether it is a implication or equivalence
-- | Function seems to be unused.
{-isImpliEquiv :: FORMULA f -> Bool
isImpliEquiv f = case (quanti f) of
                     Quantification _ _ f' _ -> isImpliEquiv f'
                     Implication _ _ _ _ -> True
                     Equivalence _ _ _ -> True
                     Negation f' _ -> isImpliEquiv f'
                     _ -> False-}


-- | check whether it's leading symbol is a operation or predication
-- | Function seems to be unused.
{-isOpPred :: FORMULA f -> Bool
isOpPred f =
    case f of
      Quantification _ _ f' _ -> isOpPred f'
      Negation f' _ -> isOpPred f'
      Implication _ f' _ _ -> isOpPred f'
      Equivalence f1 f2 _ -> isOpPred f1 && isOpPred f2
      Definedness _ _ -> False
      Predication _ _ _ -> True
      Existl_equation t _ _ -> case (term t) of
                                 Application _ _ _ -> True
                                 _ -> False
      Strong_equation t _ _ -> case (term t) of
                                 Application _ _ _ -> True
                                 _ -> False
      _ -> False-}


-- | check whether it is a application term
isApp :: TERM t -> Bool
isApp t = case t of
            Application _ _ _  -> True
            Sorted_term t' _ _ -> isApp t'
            Cast t' _ _        -> isApp t'
            _                  -> False


-- | check whether it is a Variable
isVar :: TERM t -> Bool
isVar t = case t of
            Qual_var _ _ _     -> True
            Sorted_term t' _ _ -> isVar t'
            Cast t' _ _        -> isVar t'
            _                  -> False


-- extract the operation symbol from a term
opSymbOfTerm :: TERM f -> OP_SYMB
opSymbOfTerm t = case term t of
                   Application os _ _   -> os
                   Sorted_term t' _ _   -> opSymbOfTerm t'
                   Conditional t' _ _ _ -> opSymbOfTerm t'
                   _ -> error "CASL.CCC.TermFormula.<opSymbOfTerm>"


-- | extract all variables of a term
varOfTerm :: Ord f => TERM f -> [TERM f]
varOfTerm t = case t of
                Qual_var _ _ _     -> [t]
                Sorted_term t' _ _ -> varOfTerm  t'
                Application _ ts _ -> if null ts then []
                                      else nubOrd $ concatMap varOfTerm ts
                _                  -> []


-- | extract all arguments of a term
arguOfTerm :: TERM f-> [TERM f]
arguOfTerm t = case t of
                 Qual_var _ _ _     -> [t]
                 Application _ ts _ -> ts
                 Sorted_term t' _ _ -> arguOfTerm t'
                 _                  -> []


-- | extract all arguments of a predication
arguOfPred :: FORMULA f -> [TERM f]
arguOfPred f = case quanti f of
                 Negation f1 _      -> arguOfPred f1
                 Predication _ ts _ -> ts
                 _                  -> []


-- | extract all variables of a axiom
varOfAxiom :: FORMULA f -> [VAR]
varOfAxiom f =
  case f of
    Quantification Universal v_d _ _ ->
        concatMap (\(Var_decl vs _ _)-> vs) v_d
    Quantification Existential v_d _ _ ->
        concatMap (\(Var_decl vs _ _)-> vs) v_d
    Quantification Unique_existential v_d _ _ ->
        concatMap (\(Var_decl vs _ _)-> vs) v_d
    _ -> []


-- | extract the predication symbols from a axiom
predSymbsOfAxiom :: (FORMULA f) -> [PRED_SYMB]
predSymbsOfAxiom f =
    case f of
      Quantification _ _ f' _ -> predSymbsOfAxiom f'
      Conjunction fs _ -> concatMap predSymbsOfAxiom fs
      Disjunction fs _ -> concatMap predSymbsOfAxiom fs
      Implication f1 f2 _ _ -> predSymbsOfAxiom f1 ++ predSymbsOfAxiom f2
      Equivalence f1 f2 _ -> predSymbsOfAxiom f1 ++ predSymbsOfAxiom f2
      Negation f' _ -> predSymbsOfAxiom f'
      Predication p_s _ _ -> [p_s]
      _ -> []


-- | check whether it is a partial axiom
partialAxiom :: FORMULA f -> Bool
partialAxiom f =
    case (opTypAxiom f) of
      Just False -> True
      _ -> False


-- | create the obligation of subsort
infoSubsort :: [SORT] -> FORMULA f -> [FORMULA f]
infoSubsort sts f =
    case f of
      Quantification Universal v (Equivalence (Membership _ s _) f1 _) _ ->
           [Quantification Existential v f1 nullRange | notElem s sts]
      _ -> []


-- | extract the leading symbol from a formula
leadingSym :: FORMULA f -> Maybe (Either OP_SYMB PRED_SYMB)
leadingSym = liftM extractLeadingSymb . leadingTermPredication


-- | extract the leading symbol with the range from a formula
leadingSymPos :: GetRange f => FORMULA f
              -> (Maybe (Either OP_SYMB PRED_SYMB), Range)
leadingSymPos f = leading (f,False,False,False)
  where
  leading (f1,b1,b2,b3) = case (f1,b1,b2,b3) of
                           ((Quantification _ _ f' _),_,_,_)  ->
                               leading (f',b1,b2,b3)
                           ((Negation f' _),_,_,False) ->
                               leading (f',b1,b2,True)
                           ((Implication _ f' _ _),False,False,False) ->
                               leading (f',True,False,False)
                           ((Equivalence f' _ _),_,False,False) ->
                               leading (f',b1,True,False)
                           ((Definedness t _),_,_,_) ->
                               case (term t) of
                                 Application opS _ p -> (Just (Left opS), p)
                                 _ -> (Nothing,(getRange f1))
                           ((Predication predS _ _),_,_,_) ->
                               ((Just (Right predS)),(getRange f1))
                           ((Strong_equation t _ _),_,False,False) ->
                               case (term t) of
                                 Application opS _ p -> (Just (Left opS), p)
                                 _ -> (Nothing,(getRange f1))
                           ((Existl_equation t _ _),_,False,False) ->
                               case (term t) of
                                 Application opS _ p -> (Just (Left opS), p)
                                 _ -> (Nothing,(getRange f1))
                           _ -> (Nothing,(getRange f1))


-- | extract the leading term or predication from a formula
leadingTermPredication :: FORMULA f -> Maybe (Either (TERM f) (FORMULA f))
leadingTermPredication f = leading (f,False,False,False)
  where
  leading (f1,b1,b2,b3) = case (f1,b1,b2,b3) of
                           ((Quantification _ _ f' _),_,_,_)  ->
                               leading (f',b1,b2,b3)
                           ((Negation f' _),_,_,False) ->
                               leading (f',b1,b2,True)
                           ((Implication _ f' _ _),False,False,False) ->
                               leading (f',True,False,False)
                           ((Equivalence f' _ _),_,False,False) ->
                               leading (f',b1,True,False)
                           ((Definedness t _),_,_,_) ->
                               case (term t) of
                                 Application _ _ _ -> return (Left (term t))
                                 _ -> Nothing
                           ((Predication p ts ps),_,_,_) ->
                               return (Right (Predication p ts ps))
                           ((Strong_equation t _ _),_,False,False) ->
                               case (term t) of
                                 Application _ _ _ -> return (Left (term t))
                                 _ -> Nothing
                           ((Existl_equation t _ _),_,False,False) ->
                               case (term t) of
                                 Application _ _ _ -> return (Left (term t))
                                 _ -> Nothing
                           _ -> Nothing


-- | extract the leading symbol from a term or a formula
extractLeadingSymb :: Either (TERM f) (FORMULA f) -> Either OP_SYMB PRED_SYMB
extractLeadingSymb lead =
    case lead of
      Left (Application os _ _) -> Left os
      Right (Predication p _ _) -> Right p
      _ -> error "CASL.CCC.TermFormula<extractLeadingSymb>"


-- | leadingTerm is total operation : Just True,
--   leadingTerm is partial operation : Just False,
--   others : Nothing.
opTypAxiom :: FORMULA f -> Maybe Bool
opTypAxiom f =
  case (leadingSym f) of
    Just (Left (Op_name _)) -> Nothing
    Just (Left (Qual_op_name _ (Op_type Total _ _ _) _)) -> Just True
    Just (Left (Qual_op_name _ (Op_type Partial _ _ _) _)) -> Just False
    _ -> Nothing


-- | extract the overloaded constructors
constructorOverload :: Sign f e -> OpMap -> [OP_SYMB] -> [OP_SYMB]
constructorOverload s opm os = concatMap cons_Overload os
    where cons_Overload o =
              case o of
                Op_name _ -> [o]
                Qual_op_name on1 ot _ ->
                    case Map.lookup on1 opm of
                      Nothing -> []
                      Just op_t -> concatMap (cons on1 ot)
                                   (Set.toList op_t)
          cons on opt1 opt2 = [Qual_op_name on (toOP_TYPE opt2) nullRange |
                               leqF s (toOpType opt1) opt2]


-- | check whether the operation symbol is a constructor
isCons :: Sign f e -> [OP_SYMB] -> OP_SYMB -> Bool
isCons s cons os =
    if null cons
      then False
      else is_Cons (head cons) os || isCons s (tail cons) os
    where is_Cons (Op_name _) _ = False
          is_Cons _ (Op_name _) = False
          is_Cons (Qual_op_name on1 ot1 _) (Qual_op_name on2 ot2 _)
            | on1 /= on2 = False
            | not $ isSupersort s (res_OP_TYPE ot2) (res_OP_TYPE ot1) = False
            | otherwise = isSupersortS s (args_OP_TYPE ot2) (args_OP_TYPE ot1)


-- | check whether a sort is the others super sort
isSupersort :: Sign f e -> SORT -> SORT -> Bool
isSupersort sig s1 s2 = elem s1 slist
    where sM = Rel.toMap $ sortRel sig
          slist = case Map.lookup s2 sM of
                    Nothing -> [s2]
                    Just sts -> Set.toList $ Set.insert s2 sts


-- | check whether all sorts of a set are another sets super sort
isSupersortS :: Sign f e -> [SORT] -> [SORT] -> Bool
isSupersortS sig s1 s2
    | length s1 /= length s2 = False
    | otherwise = supS s1 s2
    where supS [] [] = True
          supS sts1 sts2 = isSupersort sig (head sts1) (head sts2) &&
                           supS (tail sts1) (tail sts2)

-- | translate id to string
idStr :: Id -> String
idStr (Id ts _ _) = concatMap tokStr ts


-- | replaces variables by terms in a term
substitute :: Eq f => [(TERM f,TERM f)] -> TERM f  -> TERM f
substitute subs t =
  case t of
    t'@(Qual_var _ _ _) ->
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
        subst (x:xs) tt = if tt == snd x then fst x
                          else subst xs tt


-- | replaces variables by terms in a formula
substiF :: Eq f => [(TERM f,TERM f)] -> FORMULA f -> FORMULA f
substiF subs f =
  case f of
    Quantification q v f' r -> Quantification q v (substiF subs f') r
    Conjunction fs r -> Conjunction (map (substiF subs) fs) r
    Disjunction fs r -> Disjunction (map (substiF subs) fs) r
    Implication f1 f2 b r -> Implication (substiF subs f1) (substiF subs f2) b r
    Equivalence f1 f2 r -> Equivalence (substiF subs f1) (substiF subs f2) r
    Negation f' r -> Negation (substiF subs f') r
    Predication ps ts r -> Predication ps (map (substitute subs) ts) r
    Existl_equation t1 t2 r ->
      Existl_equation (substitute subs t1) (substitute subs t2) r
    Strong_equation t1 t2 r ->
      Strong_equation (substitute subs t1) (substitute subs t2) r
    Membership t s r -> Membership (substitute subs t) s r
    Mixfix_formula t -> Mixfix_formula (substitute subs t)
    _ -> f


-- | check whether two terms are the terms of same application symbol
sameOpsApp :: TERM f -> TERM f -> Bool
sameOpsApp app1 app2 = case (term app1) of
                          Application ops1 _ _ ->
                              case (term app2) of
                                Application ops2 _ _ -> ops1==ops2
                                _ -> False
                          _ -> False


-- | get the axiom range of a term
axiomRangeforTerm ::  (GetRange f, Eq f) => [FORMULA f] -> TERM f -> Range
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
      Conjunction fs _         -> concatVD $ nubOrd $ concatMap varDeclOfF fs
      Disjunction fs _         -> concatVD $ nubOrd $ concatMap varDeclOfF fs
      Implication f1 f2 _ _    -> concatVD $ nubOrd $ varDeclOfF f1 ++
                                  varDeclOfF f2
      Equivalence f1 f2 _      -> concatVD $ nubOrd $ varDeclOfF f1 ++
                                  varDeclOfF f2
      Negation f' _            -> varDeclOfF f'
      Predication _ ts _       -> varD $ nubOrd $ concatMap varOfTerm ts
      Definedness t _          -> varD $ varOfTerm t
      Existl_equation t1 t2 _  -> varD $ nubOrd $ varOfTerm t1 ++ varOfTerm t2
      Strong_equation t1 t2 _  -> varD $ nubOrd $ varOfTerm t1 ++ varOfTerm t2
      _ -> []
  where varD [] = []
        varD vars@(v:vs) =
            case v of
              Qual_var _ s r ->
                Var_decl (nubOrd $ map varOfV $
                           filter (\ v' -> sortOfV v' == s) vars) s r:
                varD (filter (\ v' -> sortOfV v' /= s) vs)
              _ -> error "CASL.CCC.TermFormula<varD>"
        concatVD [] = []
        concatVD vd@((Var_decl _ s r):vds) =
            Var_decl (nubOrd $ concatMap vOfVD $
                       filter (\ v' -> sortOfVarD v' == s) vd) s r:
            concatVD (filter (\ v' -> sortOfVarD v' /= s) vds)
        vOfVD (Var_decl vs _ _) = vs
        sortOfV (Qual_var _ s _) = s
        sortOfV _ = error "CASL.CCC.TermFormula<sortOfV>"
        varOfV (Qual_var v _ _) = v
        varOfV _ = error "CASL.CCC.TermFormula<varOfV>"
