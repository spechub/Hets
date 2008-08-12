{- |
Module      :  $Header$
Description :  translate CASL to S-Expressions
Copyright   :  (c) C. Maeder, DFKI 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

translation of CASL to S-Expressions
-}

module CASL.ToSExpr where

import CASL.Fold
import CASL.Sign
import CASL.AS_Basic_CASL
import CASL.Quantification
import Common.SExpr
import Common.Result
import Common.Id

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as List

predToSSymbol :: Sign f e -> PRED_SYMB -> SExpr
predToSSymbol sign p = case p of
    Pred_name _ -> error "predToSSymbol"
    Qual_pred_name i t _ -> predIdToSSymbol sign i $ toPredType t

predIdToSSymbol :: Sign f e -> Id -> PredType -> SExpr
predIdToSSymbol sign i t = case Map.lookup i $ predMap sign of
    Nothing -> error "predIdToSSymbol"
    Just s -> case List.elemIndex t $ Set.toList s of
      Nothing -> error "predIdToSSymbol2"
      Just n -> idToSSymbol (n + 1) i

opToSSymbol :: Sign f e -> OP_SYMB -> SExpr
opToSSymbol sign o = case o of
    Op_name _ -> error "opToSSymbol"
    Qual_op_name i t _ -> opIdToSSymbol sign i $ toOpType t

opIdToSSymbol :: Sign f e -> Id -> OpType -> SExpr
opIdToSSymbol sign i (OpType _ args res) = case Map.lookup i $ opMap sign of
    Nothing -> error $ "opIdToSSymbol " ++ show i
    Just s -> case List.findIndex
      (\ r -> opArgs r == args && opRes r == res) $ Set.toList s of
        Nothing -> error "opIdToSSymbol2"
        Just n -> idToSSymbol (n + 1) i

sortToSSymbol :: Id -> SExpr
sortToSSymbol = idToSSymbol 0

varToSSymbol :: Token -> SExpr
varToSSymbol = SSymbol . transToken

varDeclToSExpr :: (VAR, SORT) -> SExpr
varDeclToSExpr (v, s) =
  SList [SSymbol "vardecl-indet", varToSSymbol v, sortToSSymbol s]

sfail :: String -> Range -> a
sfail s r = error $ show (Diag Error ("unexpected " ++ s) r)

sRec :: Sign a e -> (f -> SExpr)
     -> Record f SExpr SExpr
sRec sign mf = Record
    { foldQuantification = \ _ q vs f _ ->
        let s = SSymbol $ case q of
              Universal -> "all"
              Existential -> "ex"
              Unique_existential -> "ex1"
            vl = SList $ map varDeclToSExpr $ flatVAR_DECLs vs
        in SList [s, vl, f]
    , foldConjunction = \ _ fs _ -> SList $ SSymbol "and" : fs
    , foldDisjunction = \ _ fs _ -> SList $ SSymbol "or" : fs
    , foldImplication = \ _ f1 f2 b _ ->
        SList $ SSymbol "implies" : if b then [f1, f2] else [f2, f1]
    , foldEquivalence = \ _ f1 f2 _ -> SList [SSymbol "equiv", f1, f2]
    , foldNegation = \ _ f _ -> SList [SSymbol "not", f]
    , foldTrue_atom = \ _ _ -> SSymbol "true"
    , foldFalse_atom = \ _ _ -> SSymbol "false"
    , foldPredication = \ _ p ts _ ->
        SList $ SSymbol "papply" : predToSSymbol sign p : ts
    , foldDefinedness = \ _ t _ -> SList [SSymbol "def", t]
    , foldExistl_equation = \ _ t1 t2 _ -> SList [SSymbol "eeq", t1, t2]
    , foldStrong_equation = \ _ t1 t2 _ -> SList [SSymbol "eq", t1, t2]
    , foldMembership = \ _ t s _ ->
        SList [SSymbol "member", t, sortToSSymbol s]
    , foldMixfix_formula = \ t _ -> sfail "Mixfix_formula" $ getRange t
    , foldSort_gen_ax = \ _ cs b ->
      let (srts, ops, _) = recover_Sort_gen_ax cs in
      SList $ SSymbol ((if b then "freely-" else "") ++ "generated")
        : (case srts of
            [s] -> sortToSSymbol s
            _ -> SList $ map sortToSSymbol srts)
        : map (opToSSymbol sign) ops
    , foldExtFORMULA = \ _ f -> mf f
    , foldSimpleId = \ _ t -> sfail "Simple_id" $ tokPos t
    , foldQual_var = \ _ v _ _ ->
        SList [SSymbol "varterm", varToSSymbol v]
    , foldApplication = \ _ o ts _ ->
        SList $ SSymbol "fapply" : opToSSymbol sign o : ts
    , foldSorted_term = \ _ r _ _ -> r
    , foldCast = \ _ t s _ -> SList [SSymbol "cast", t, sortToSSymbol s]
    , foldConditional = \ _ e f t _ -> SList [SSymbol "condition", e, f, t]
    , foldMixfix_qual_pred = \ _ p -> sfail "Mixfix_qual_pred" $ getRange p
    , foldMixfix_term = \ (Mixfix_term ts) _ ->
        sfail "Mixfix_term" $ getRange ts
    , foldMixfix_token = \ _ t -> sfail "Mixfix_token" $ tokPos t
    , foldMixfix_sorted_term = \ _ _ r -> sfail "Mixfix_sorted_term" r
    , foldMixfix_cast = \ _ _ r -> sfail "Mixfix_cast" r
    , foldMixfix_parenthesized = \ _ _ r -> sfail "Mixfix_parenthesized" r
    , foldMixfix_bracketed = \ _ _ r -> sfail "Mixfix_bracketed" r
    , foldMixfix_braced = \ _ _ r -> sfail "Mixfix_braced" r }

signToSExprs :: Sign a e -> [SExpr]
signToSExprs sign = sortSignToSExprs sign
  : predMapToSExprs sign (predMap sign) ++ opMapToSExprs sign (opMap sign)

sortSignToSExprs :: Sign a e -> SExpr
sortSignToSExprs sign =
    SList (SSymbol "sorts"
      : map sortToSSymbol (Set.toList $ sortSet sign))

predMapToSExprs :: Sign a e -> Map.Map Id (Set.Set PredType) -> [SExpr]
predMapToSExprs sign pm =
    concatMap (\ (p, ts) -> map (\ t ->
       SList [ SSymbol "predicate"
             , predIdToSSymbol sign p t
             , SList $ map sortToSSymbol $ predArgs t ]) $ Set.toList ts)
      $ Map.toList pm

opMapToSExprs :: Sign a e -> OpMap -> [SExpr]
opMapToSExprs sign om =
    concatMap (\ (p, ts) -> map (\ t ->
       SList [ SSymbol "function"
             , opIdToSSymbol sign p t
             , SList $ map sortToSSymbol $ opArgs t
             , sortToSSymbol $ opRes t ]) $ Set.toList ts)
      $ Map.toList om
