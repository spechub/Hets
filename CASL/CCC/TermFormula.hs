{- |
Module      :  $Header$
Description :  auxiliary functions on terms and formulas
Copyright   :  (c) Mingyi Liu and Till Mossakowski and Uni Bremen 2004-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  xinga@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Auxiliary functions on terms and formulas
-}

module CASL.CCC.TermFormula where

import CASL.AS_Basic_CASL
import CASL.Overload
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel
import CASL.Sign
import Common.AS_Annotation
import Common.Id
import Data.List (nub)
-- import Common.DocUtils


-- | the sorted term is always ignored
term :: TERM f -> TERM f
term t = case t of
           Sorted_term t' _ _ ->term t'
           _ -> t


-- | the quantifier of term is always ignored
quanti :: FORMULA f -> FORMULA f
quanti f = case f of
             Quantification _ _ f' _ -> quanti f'
             _ -> f


-- | check whether it exist a (unique)existent quantification
is_ex_quanti :: FORMULA f -> Bool
is_ex_quanti f =
    case f of
      Quantification Existential _ _ _ -> True
      Quantification Unique_existential _ _ _ -> True
      Quantification _ _ f' _ -> is_ex_quanti f'
      Implication f1 f2 _ _ -> (is_ex_quanti f1) || (is_ex_quanti f2)
      Equivalence f1 f2 _ -> (is_ex_quanti f1) || (is_ex_quanti f2)
      Negation f' _ -> is_ex_quanti f'
      _ -> False


-- | get the constraint from a sort generated axiom
constraintOfAxiom :: FORMULA f -> [Constraint]
constraintOfAxiom f =
    case f of
      Sort_gen_ax constrs _ -> constrs
      _ ->[]


is_user_or_sort_gen :: Named (FORMULA f) -> Bool
is_user_or_sort_gen ax = take 12 name == "ga_generated" ||
                         take 3 name /= "ga_"
    where name = senAttr ax


-- | determine whether a formula is a sort generation constraint
isSortGen :: FORMULA a -> Bool
isSortGen (Sort_gen_ax _ _) = True
isSortGen _ = False


-- | check whether it contains a membership formula
is_Membership :: FORMULA f -> Bool
is_Membership f =
  case f of
    Quantification _ _ f' _ -> is_Membership f'
    Conjunction fs _ -> any is_Membership fs
    Disjunction fs _ -> any is_Membership fs
    Negation f' _ -> is_Membership f'
    Implication f1 f2 _ _ -> is_Membership f1 || is_Membership f2
    Equivalence f1 f2 _ -> is_Membership f1 || is_Membership f2
    Membership _ _ _ -> True
    _ -> False


-- | check whether a sort is free generated
is_free_gen_sort :: SORT -> [FORMULA f] -> Maybe Bool
is_free_gen_sort _ [] = Nothing
is_free_gen_sort s (f:fs) =
  case f of
    Sort_gen_ax csts isFree
      | any ((== s) . newSort) csts
        -> Just isFree
    _ -> is_free_gen_sort s fs


-- | check whether it is the domain of a partial function
isDomain :: FORMULA f -> Bool
isDomain f = case (quanti f) of
               Equivalence (Definedness _ _) f' _ ->
                 if containDef f' then False
                 else True
               Definedness _ _ -> True
               _ -> False


-- | check whether it contains a definedness formula
containDef :: FORMULA f -> Bool
containDef f = case f of
             Quantification _ _ f' _ -> containDef f'
             Conjunction fs _ -> any containDef fs
             Disjunction fs _ -> any containDef fs
             Implication f1 f2 _ _ -> containDef f1 || containDef f2
             Equivalence f1 f2 _ -> containDef f1 || containDef f2
             Negation f' _ -> containDef f'
             Definedness _ _ -> True
             _ -> False


-- | check whether it contains a negation
containNeg :: FORMULA f -> Bool
containNeg f = case f of
                 Quantification _ _ f' _ -> containNeg f'
                 Implication _ f' _ _ -> containNeg f'
                 Equivalence f' _ _ -> containNeg f'
                 Negation _ _ -> True
                 _ -> False


-- | check whether it contains a definedness formula in correct form
correctDef :: FORMULA f -> Bool
correctDef f = case (quanti f) of
             Implication _ (Definedness _ _) _ _ -> False
             Implication (Definedness _ _) _ _ _ -> True
             Equivalence (Definedness _ _) f' _ ->
               if containDef f' then False
               else True
             Negation (Definedness _ _) _ -> True
             Definedness _ _ -> True
             _ -> False


-- | extract all partial function symbols, their domains are defined
domainOpSymbs :: [FORMULA f] -> [OP_SYMB]
domainOpSymbs fs = concat $ map domOpS fs
  where domOpS f = case (quanti f) of
                     Equivalence (Definedness t _) _ _ ->
                       [opSymbOfTerm t]
                     _ -> []


-- | check whether a formula gives the domain of a partial function
domain_os :: FORMULA f -> OP_SYMB -> Bool
domain_os f os = case (quanti f) of
                   Equivalence (Definedness t _) _ _ ->
                     opSymbOfTerm t == os
                   _ -> False


-- | extract the domain-list of partial functions
domainList :: [FORMULA f] -> [(TERM f,FORMULA f)]
domainList fs = concat $ map dm fs
  where dm f = case (quanti f) of
                 Equivalence (Definedness t _) f' _ ->
                   [(t,f')]
                 _ -> []


-- | check whether it is a implication
is_impli :: FORMULA f -> Bool
is_impli f = case (quanti f) of
               Quantification _ _ f' _ -> is_impli_equiv f'
               Implication _ _ _ _ -> True
               Negation f' _ -> is_impli_equiv f'
               _ -> False


-- | check whether it is a implication or equivalence
is_impli_equiv :: FORMULA f -> Bool
is_impli_equiv f = case (quanti f) of
                     Quantification _ _ f' _ -> is_impli_equiv f'
                     Implication _ _ _ _ -> True
                     Equivalence _ _ _ -> True
                     Negation f' _ -> is_impli_equiv f'
                     _ -> False


-- | check whether it's leading symbol is a operation or predication
isOp_Pred :: FORMULA f -> Bool
isOp_Pred f =
    case f of
      Quantification _ _ f' _ -> isOp_Pred f'
      Negation f' _ -> isOp_Pred f'
      Implication _ f' _ _ -> isOp_Pred f'
      Equivalence f1 f2 _ -> (isOp_Pred f1) && (isOp_Pred f2)
      Definedness _ _ -> False
      Predication _ _ _ -> True
      Existl_equation t _ _ -> case (term t) of
                                 Application _ _ _ -> True
                                 _ -> False
      Strong_equation t _ _ -> case (term t) of
                                 Application _ _ _ -> True
                                 _ -> False
      _ -> False


-- | check whether it is a application term
isApp :: TERM t -> Bool
isApp t = case t of
            Application _ _ _-> True
            Sorted_term t' _ _ -> isApp t'
            Cast t' _ _ -> isApp t'
            _ -> False


-- | check whether it is a Variable
isVar :: TERM t -> Bool
isVar t = case t of
            Qual_var _ _ _ -> True
            Sorted_term t' _ _ -> isVar t'
            Cast t' _ _ -> isVar t'
            _ -> False


-- extract the operation symbol from a term
opSymbOfTerm :: TERM f -> OP_SYMB
opSymbOfTerm t = case term t of
                   Application os _ _ -> os
                   Sorted_term t' _ _ -> opSymbOfTerm t'
                   Conditional t' _ _ _ -> opSymbOfTerm t'
                   _ -> error "CASL.CCC.TermFormula.<opSymbOfTerm>"


-- | extract all variables of a term
varOfTerm :: Eq f => TERM f -> [TERM f]
varOfTerm t = case t of
                Qual_var _ _ _ -> [t]
                Sorted_term t' _ _ -> varOfTerm  t'
                Application _ ts _ -> if length ts==0 then []
                                      else nub $ concat $ map varOfTerm ts
                _ -> []


-- | extract all arguments of a term
arguOfTerm :: TERM f-> [TERM f]
arguOfTerm t = case t of
                 Qual_var _ _ _ -> [t]
                 Application _ ts _ -> ts
                 Sorted_term t' _ _ -> arguOfTerm t'
                 _ -> []


-- | extract all arguments of a predication
arguOfPred :: FORMULA f -> [TERM f]
arguOfPred f = case quanti f of
                 Negation f1 _ -> arguOfPred f1
                 Predication _ ts _ -> ts
                 _ -> []


-- | extract all variables of a axiom
varOfAxiom :: FORMULA f -> [VAR]
varOfAxiom f =
  case f of
    Quantification Universal v_d _ _ ->
        concat $ map (\(Var_decl vs _ _)-> vs) v_d
    Quantification Existential v_d _ _ ->
        concat $ map (\(Var_decl vs _ _)-> vs) v_d
    Quantification Unique_existential v_d _ _ ->
        concat $ map (\(Var_decl vs _ _)-> vs) v_d
    _ -> []


-- | extract the predication symbols from a axiom
predSymbsOfAxiom :: (FORMULA f) -> [PRED_SYMB]
predSymbsOfAxiom f =
    case f of
      Quantification _ _ f' _ ->
          predSymbsOfAxiom f'
      Conjunction fs _ ->
          concat $ map predSymbsOfAxiom fs
      Disjunction fs _ ->
          concat $ map predSymbsOfAxiom fs
      Implication f1 f2 _ _ ->
          (predSymbsOfAxiom f1) ++ (predSymbsOfAxiom f2)
      Equivalence f1 f2 _ ->
          (predSymbsOfAxiom f1) ++ (predSymbsOfAxiom f2)
      Negation f' _ ->
          predSymbsOfAxiom f'
      Predication p_s _ _ -> [p_s]
      _ -> []


-- | check whether it is a partial axiom
partialAxiom :: FORMULA f -> Bool
partialAxiom f =
    case (opTyp_Axiom f) of
      Just False -> True
      _ -> False


-- | create the obligation of subsort
infoSubsort :: [SORT] -> FORMULA f -> [FORMULA f]
infoSubsort sts f =
    case f of
      Quantification Universal v (Equivalence (Membership _ s _) f1 _) _ ->
          if not $ elem s sts
          then [Quantification Existential v f1 nullRange]
          else []
      _ -> []


-- | extract the leading symbol from a formula
leadingSym :: FORMULA f -> Maybe (Either OP_SYMB PRED_SYMB)
leadingSym f = do
  tp<-leading_Term_Predication f
  return (extract_leading_symb tp)


-- | extract the leading symbol with the range from a formula
leadingSymPos :: GetRange f => FORMULA f
              -> (Maybe (Either OP_SYMB PRED_SYMB), Range)
leadingSymPos f = leading (f,False,False,False)
  where
  leading (f1,b1,b2,b3)= case (f1,b1,b2,b3) of
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
leading_Term_Predication :: FORMULA f -> Maybe (Either (TERM f) (FORMULA f))
leading_Term_Predication f = leading (f,False,False,False)
  where
  leading (f1,b1,b2,b3)= case (f1,b1,b2,b3) of
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
                                 Application _ _ _ ->
                                   return (Left (term t))
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
extract_leading_symb :: Either (TERM f) (FORMULA f) -> Either OP_SYMB PRED_SYMB
extract_leading_symb lead =
    case lead of
      Left (Application os _ _) -> Left os
      Right (Predication p _ _) -> Right p
      _ -> error "CASL.CCC.TermFormula<extract_leading_symb>"


-- | leadingTerm is total operation : Just True,
--   leadingTerm is partial operation : Just False,
--   others : Nothing.
opTyp_Axiom :: FORMULA f -> Maybe Bool
opTyp_Axiom f =
  case (leadingSym f) of
    Just (Left (Op_name _)) -> Nothing
    Just (Left (Qual_op_name _ (Op_type Total _ _ _) _)) -> Just True
    Just (Left (Qual_op_name _ (Op_type Partial _ _ _) _)) -> Just False
    _ -> Nothing


-- | extract the overloaded constructors
constructorOverload :: Sign f e -> OpMap -> [OP_SYMB] -> [OP_SYMB]
constructorOverload s opm os = concat $ map (\ o1 -> cons_Overload o1) os
    where cons_Overload o =
              case o of
                Op_name _ -> [o]
                Qual_op_name on1 ot _ ->
                    case Map.lookup on1 opm of
                      Nothing -> []
                      Just op_t -> concat $ map (\opt->cons on1 ot opt) $
                                   (Set.toList $ op_t)
          cons on opt1 opt2 =
              case (leqF s (toOpType opt1) opt2) of
                True -> [(Qual_op_name on (toOP_TYPE opt2) nullRange)]
                False -> []


-- | check whether the operation symbol is a constructor
isCons :: Sign f e -> [OP_SYMB] -> OP_SYMB -> Bool
isCons s cons os =
    case cons of
      [] -> False
      _ -> if is_Cons (head cons) os then True
           else isCons s (tail cons) os
    where is_Cons (Op_name _) _ = False
          is_Cons _ (Op_name _) = False
          is_Cons (Qual_op_name on1 ot1 _) (Qual_op_name on2 ot2 _)
            | on1 /= on2 = False
            | not $ isSupersort s (res_OP_TYPE ot2) (res_OP_TYPE ot1) = False
            | otherwise = isSupersortS s (args_OP_TYPE ot2) (args_OP_TYPE ot1)


-- | check whether a sort is the others super sort
isSupersort :: Sign f e -> SORT -> SORT -> Bool
isSupersort sig s1 s2 = elem s1 slist
    where sM = Rel.toMap $ sortRel $ sig
          slist = case Map.lookup s2 sM of
                    Nothing -> [s2]
                    Just sts -> Set.toList $ Set.insert s2 sts


-- | check whether all sorts of a set are another sets super sort
isSupersortS :: Sign f e -> [SORT] -> [SORT] -> Bool
isSupersortS sig s1 s2
    | length s1 /= length s2 = False
    | otherwise = supS s1 s2
    where supS [] [] = True
          supS sts1 sts2 = if isSupersort sig (head sts1) (head sts2)
                           then supS (tail sts1) (tail sts2)
                           else False


-- | translate id to string
idStr :: Id -> String
idStr (Id ts _ _) = concat $ map tokStr ts


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
        subst (x:xs) tt = if tt == (snd x) then (fst x)
                          else subst xs tt


-- | replaces variables by terms in a formula
substiF :: Eq f => [(TERM f,TERM f)] -> FORMULA f -> FORMULA f
substiF subs f =
  case f of
    Quantification q v f' r ->
      Quantification q v (substiF subs f') r
    Conjunction fs r ->
      Conjunction (map (substiF subs) fs) r
    Disjunction fs r ->
      Disjunction (map (substiF subs) fs) r
    Implication f1 f2 b r ->
      Implication (substiF subs f1) (substiF subs f2) b r
    Equivalence f1 f2 r ->
      Equivalence (substiF subs f1) (substiF subs f2) r
    Negation f' r -> Negation (substiF subs f') r
    Predication ps ts r ->
      Predication ps (map (substitute subs) ts) r
    Existl_equation t1 t2 r ->
      Existl_equation (substitute subs t1) (substitute subs t2) r
    Strong_equation t1 t2 r ->
      Strong_equation (substitute subs t1) (substitute subs t2) r
    Membership t s r -> Membership (substitute subs t) s r
    Mixfix_formula t -> Mixfix_formula (substitute subs t)
    _ -> f


-- | check whether two terms are the terms of same application symbol
sameOps_App :: TERM f -> TERM f -> Bool
sameOps_App app1 app2 = case (term app1) of
                          Application ops1 _ _ ->
                              case (term app2) of
                                Application ops2 _ _ -> ops1==ops2
                                _ -> False
                          _ -> False


-- | check whether a string is a substring of another
subStr :: String -> String -> Bool
subStr [] _ = True
subStr _ [] = False
subStr xs ys = if (head xs) == (head ys) &&
                  xs == take (length xs) ys then True
               else subStr xs (tail ys)


-- | get the axiom range of a term
axiomRangeforTerm ::  (GetRange f, Eq f) => [FORMULA f] -> TERM f -> Range
axiomRangeforTerm [] _ = nullRange
axiomRangeforTerm fs t =
    case leading_Term_Predication (head fs) of
      Just (Left tt) -> case (tt==t) of
                          True -> getRange $ quanti $ head fs
                          False -> axiomRangeforTerm (tail fs) t
      _ -> axiomRangeforTerm (tail fs) t


-- | get the sort of a variable declaration
sortOfVarD :: VAR_DECL -> SORT
sortOfVarD (Var_decl _ s _) = s


-- | get or create a variable declaration for a formula
varDeclOfF :: Eq f => FORMULA f -> [VAR_DECL]
varDeclOfF f =
    case f of
      Quantification _ vds _ _ -> vds
      Conjunction fs _ ->
        concatVD $ nub $ concat $ map varDeclOfF fs
      Disjunction fs _ ->
        concatVD $ nub $ concat $ map varDeclOfF fs
      Implication f1 f2 _ _ ->
        concatVD $ nub $ (varDeclOfF f1) ++ (varDeclOfF f2)
      Equivalence f1 f2 _ ->
        concatVD $ nub $ (varDeclOfF f1) ++ (varDeclOfF f2)
      Negation f' _ ->
        varDeclOfF f'
      Predication _ ts _ ->
        varD $ nub $ concat $ map varOfTerm ts
      Definedness t _ ->
        varD $ varOfTerm t
      Existl_equation t1 t2 _ ->
        varD $ nub $ (varOfTerm t1) ++ (varOfTerm t2)
      Strong_equation t1 t2 _ ->
        varD $ nub $ (varOfTerm t1) ++ (varOfTerm t2)
      _ -> []
  where varD [] = []
        varD vars@(v:vs) =
            case v of
              Qual_var _ s r ->
                (Var_decl (nub $ map varOfV $
                           filter (\v'-> (sortOfV v') == s) vars) s r):
                (varD $ filter (\v'-> (sortOfV v') /= s) vs)
              _ -> error "CASL.CCC.TermFormula<varD>"
        concatVD [] = []
        concatVD vd@((Var_decl _ s r):vds) =
            (Var_decl (nub $ concat $ map vOfVD $
                       filter (\v'-> (sortOfVarD v') == s) vd) s r):
            (concatVD $ filter (\v'-> (sortOfVarD v') /= s) vds)
        vOfVD (Var_decl vs _ _) = vs
        sortOfV (Qual_var _ s _) = s
        sortOfV _ = error "CASL.CCC.TermFormula<sortOfV>"
        varOfV (Qual_var v _ _) = v
        varOfV _ = error "CASL.CCC.TermFormula<varOfV>"
