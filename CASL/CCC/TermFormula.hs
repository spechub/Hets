{- | 
Module      :  $Header$
Description :  auxiliary functions on terms and formulas
Copyright   :  (c) Mingyi Liu and Till Mossakowski and Uni Bremen 2004-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  xinga@tzi.de
Stability   :  provisional
Portability :  portable

Aauxiliary functions on terms and formulas
-}

module CASL.CCC.TermFormula where
                        
import CASL.AS_Basic_CASL
import CASL.Overload
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import CASL.Sign       
import Common.AS_Annotation
import Common.Id
-- import Debug.Trace
-- import Common.DocUtils

-- | Sorted_term is always ignored
term :: TERM f -> TERM f
term t = case t of
           Sorted_term t' _ _ ->term t'
           _ -> t


-- | Quantifier is always ignored
quanti :: FORMULA f -> FORMULA f
quanti f = case f of
             Quantification _ _ f' _ -> quanti f'
             _ -> f


-- | check whether it is a existent quantification
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
      Sort_gen_ax constrs True -> constrs
      _ ->[]


-- | check whether it is a parial operation symbol                        
partial_OpSymb :: OP_SYMB -> Maybe Bool
partial_OpSymb os = 
    case os of
      Op_name _ -> Nothing
      Qual_op_name _ ot _ -> case ot of
                               Op_type Total _ _ _ -> Just False
                               Op_type Partial _ _ _ -> Just True


is_user_or_sort_gen :: Named (FORMULA f) -> Bool
is_user_or_sort_gen ax = take 12 name == "ga_generated" || 
                         take 3 name /= "ga_"
    where name = senName ax     


-- | check whether it is a Membership formula
is_Membership :: FORMULA f -> Bool
is_Membership f =
  case f of
    Quantification _ _ f' _ -> is_Membership f'
    Equivalence f' _ _ -> is_Membership f'
    Membership _ _ _ -> True
    _ -> False


-- | check whether it is a sort generated formula
is_Sort_gen_ax :: FORMULA f -> Bool
is_Sort_gen_ax f = case f of
                     Sort_gen_ax _ _ -> True
                     _ -> False   


-- | check whether it is a Definedness formula
is_Def :: FORMULA f -> Bool
is_Def f = case (quanti f) of
             Implication (Definedness _ _) _ _ _ -> True
             Equivalence (Definedness _ _) _ _ -> True
             Negation (Definedness _ _) _ -> True
             Definedness _ _ -> True
             _ -> False


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


-- | check whether it is a operation or predication
isOp_Pred :: FORMULA f -> Bool
isOp_Pred f = 
    case f of
      Quantification _ _ f' _ -> isOp_Pred f'
      Negation f' _ -> isOp_Pred f'
      Implication _ f' _ _ -> isOp_Pred f'
      Equivalence f' _ _ -> isOp_Pred f'
      Definedness t _ -> case (term t) of
                           Application _ _ _ -> True
                           _ -> False
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
            Application _ _ _->True
            Sorted_term t' _ _ ->isApp t'
            _ -> False


-- | check whether it is a Variable
isVar :: TERM t -> Bool
isVar t = case t of
            Qual_var _ _ _ ->True
            Sorted_term t' _ _ ->isVar t'
            _ -> False


-- | extract all variables of a term
allVarOfTerm :: TERM f -> [TERM f]
allVarOfTerm t = case t of
                   Qual_var _ _ _ -> [t]
                   Sorted_term t' _ _ -> allVarOfTerm  t'
                   Application _ ts _ -> if length ts==0 then []
                                         else concat $ map allVarOfTerm ts
                   _ -> []


-- | extract all Argument of a term
allArguOfTerm :: TERM f-> [TERM f]
allArguOfTerm t = case t of
                    Qual_var _ _ _ -> [t]
                    Application _ ts _ -> ts
                    Sorted_term t' _ _ -> allArguOfTerm t'
                    Cast t' _ _ -> allArguOfTerm t'
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
    case f of
      Quantification _ _ f' _ -> partialAxiom f'
      Negation f' _ ->
          case f' of
            Definedness t _ -> 
                case (term t) of
                  Application opS _ _ -> 
                      case (partial_OpSymb opS) of
                        Just True -> True
                        _ -> False
                  _ -> False
            _ -> False
      Implication f' _ _ _ -> 
          case f' of
            Definedness t _ -> 
                case (term t) of
                  Application opS _ _ -> 
                      case (partial_OpSymb opS) of
                        Just True -> True
                        _ -> False
                  _ -> False
            _ -> False
      Equivalence f' _ _ -> 
          case f' of
            Definedness t _ -> 
                case (term t) of
                  Application opS _ _ -> 
                      case (partial_OpSymb opS) of
                        Just True -> True
                        _ -> False
                  _ -> False
            _ -> False
      _ -> False                    


-- | creat the information of subsort
infoSubsort :: FORMULA f -> FORMULA f
infoSubsort f =
    case f of
      Quantification Universal v (Equivalence _ f1 _) _ ->
          Quantification Existential v f1 nullRange
      _ -> error "CASL.CCC.TermFormula.<infoSubsort>" 


-- | extract the leading symbol from a formula
leadingSym :: FORMULA f -> Maybe (Either OP_SYMB PRED_SYMB)
leadingSym f = do
  tp<-leading_Term_Predication f
  return (extract_leading_symb tp)
 

-- | extract the leading symbol with the range from a formula
leadingSymPos :: PosItem f => FORMULA f 
              -> (Maybe (Either OP_SYMB PRED_SYMB), Range)
leadingSymPos f = leading (f,False,False)
  where 
  leading (f1,b1,b2)= case (f1,b1,b2) of
                       ((Quantification _ _ f' _),_,_)  -> 
                           leading (f',b1,b2)
                       ((Negation f' _),_,_) -> 
                           leading (f',b1,b2)
                       ((Implication _ f' _ _),False,False) -> 
                           leading (f',True,False)
                       ((Equivalence f' _ _),_,False) -> 
                           leading (f',b1,True)
                       ((Definedness t _),_,_) -> 
                           case (term t) of
                             Application opS _ p -> (Just (Left opS), p)
                             _ -> (Nothing,(getRange f1))
                       ((Predication predS _ _),_,_) -> 
                           ((Just (Right predS)),(getRange f1))
                       ((Strong_equation t _ _),_,_) -> 
                           case (term t) of
                             Application opS _ p -> (Just (Left opS), p)
                             _ -> (Nothing,(getRange f1))
                       ((Existl_equation t _ _),_,_) -> 
                           case (term t) of
                             Application opS _ p -> (Just (Left opS), p)
                             _ -> (Nothing,(getRange f1))
                       _ -> (Nothing,(getRange f1)) 


-- | extract the leading term or predication from a formula
leading_Term_Predication :: FORMULA f -> Maybe (Either (TERM f) (FORMULA f))
leading_Term_Predication f = leading (f,False,False)
  where 
  leading (f1,b1,b2)= case (f1,b1,b2) of
                       ((Quantification _ _ f' _),_,_)  -> 
                           leading (f',b1,b2)     
                       ((Negation f' _),_,_) -> 
                           leading (f',b1,b2)
                       ((Implication _ f' _ _),False,False) -> 
                           leading (f',True,False)
                       ((Equivalence f' _ _),_,False) -> 
                           leading (f',b1,True)
                       ((Definedness t _),_,_) -> case (term t) of
                                                    Application _ _ _ -> 
                                                        return (Left (term t))
                                                    _ -> Nothing
                       ((Predication p ts ps),_,_) -> 
                           return (Right (Predication p ts ps))
                       ((Strong_equation t _ _),_,_) -> 
                           case (term t) of
                             Application _ _ _ -> return (Left (term t))
                             _ -> Nothing
                       ((Existl_equation t _ _),_,_) -> 
                           case (term t) of
                             Application _ _ _ -> return (Left (term t))
                             _ -> Nothing
                       _ -> Nothing
 

-- | extract the leading symbol from a term or a formula
extract_leading_symb :: Either (TERM f) (FORMULA f) -> Either OP_SYMB PRED_SYMB
extract_leading_symb lead = case lead of
                              Left (Application os _ _) -> Left os
                              Right (Predication p _ _) -> Right p
                              _ -> error "CASL.CCC.TermFormula<extract_leading_symb>"


-- | leadingTerm is total operation : Just True
--   leadingTerm is partial operation : Just False
--   others : Nothing
opTyp_Axiom :: FORMULA f -> Maybe Bool
opTyp_Axiom f = 
  case (leadingSym f) of
    Just (Left (Op_name _)) -> Nothing
    Just (Left (Qual_op_name _ (Op_type Total _ _ _) _)) -> Just True 
    Just (Left (Qual_op_name _ (Op_type Partial _ _ _) _)) -> Just False  
    _ -> Nothing 

-- | extract the OP_SYMB from a application term
opSymbOfTerm :: TERM f -> OP_SYMB
opSymbOfTerm t = 
  case t of
    Application os _ _ -> os
    _ -> error "CASL.CCC.TermFormula<opSymbOfTerm>"



-- constructorOverload :: Sign f e -> Sign f e -> [OP_SYMB] -> [OP_SYMB]
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



-- | transform id to string
idStr :: Id -> String
idStr (Id ts _ _) = concat $ map tokStr ts 


-- | each element of a list occurs only once
everyOnce :: (Eq a) => [a] -> [a]
everyOnce [] = []
everyOnce (x:xs) = x:(everyOnce $ filter (\a-> a /= x ) xs)


-- | check whether a string is a substring of another
subStr :: String -> String -> Bool
subStr [] _ = True
subStr _ [] = False
subStr xs ys = if (head xs) == (head ys) &&
                  xs == take (length xs) ys then True
               else subStr xs (tail ys)


-- | filter the element of list2 from list1, return list1
diffList :: (Eq a) => [a] -> [a] -> [a]
diffList [] _ = []
diffList l [] = l
diffList (l:ls) a = if elem l a
                    then diffList ls a
                    else l:(diffList ls a)

