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
import CASL.AS_Basic_CASL
import Common.SExpr
import Common.Result
import Common.Id

predToSSymbol :: PRED_SYMB -> SExpr
predToSSymbol = undefined

opToSSymbol :: OP_SYMB -> SExpr
opToSSymbol = undefined

varToSSymbol :: Token -> SExpr
varToSSymbol = SSymbol . tokStr

sfail :: Monad m => String -> m a
sfail s = fail $ "unexpected " ++ s

sRec :: Bool -> (f -> Result SExpr) -> Record f (Result SExpr) (Result SExpr)
sRec withQuant mf = Record
    { foldQuantification = \ _ q vs r _ -> if withQuant then do
        s <- case q of
          Unique_existential -> sfail "Unique_existential"
          _ -> return $ SSymbol $ case q of
            Universal -> "all"
            Existential -> "ex"
            _ -> ""
        let vl = SList []
        f <- r
        return $ SList $ s : vl : [f]
      else sfail "Quantification"
    , foldConjunction = \ _ rs _ -> do
      fs <- sequence rs
      return $ SList $ SSymbol "and" : fs
    , foldDisjunction = \ _ rs _ -> do
      fs <- sequence rs
      return $ SList $ SSymbol "or" : fs
    , foldImplication = \ _ r1 r2 b _ -> do
      f1 <- r1
      f2 <- r2
      return $ SList $ SSymbol "implies" : if b then f1 : [f2] else f2 : [f1]
    , foldEquivalence = \ _ r1 r2 _ -> do
      f1 <- r1
      f2 <- r2
      return $ SList $ SSymbol "equiv" : f1 : [f2]
    , foldNegation = \ _ r _ -> do
      f <- r
      return $ SList $ SSymbol "not" : [f]
    , foldTrue_atom = \ _ _ -> return $ SSymbol "true"
    , foldFalse_atom = \ _ _ -> return $ SSymbol "false"
    , foldPredication = \ _ p rs _ -> do
      ts <- sequence rs
      return $ SList $ SSymbol "papply" : predToSSymbol p : ts
    , foldDefinedness = \ _ _ _ -> sfail "Definedness"
    , foldExistl_equation = \ _ _ _ _ -> sfail "Existl_equation"
    , foldStrong_equation = \ _ r1 r2 _ -> do
      t1 <- r1
      t2 <- r2
      return $ SList $ SSymbol "eq" : t1 : [t2]
    , foldMembership = \ _ _ _ _ -> sfail "Membership"
    , foldMixfix_formula = \ _ _ -> sfail "Mixfix_formula"
    , foldSort_gen_ax = \ _ _ _ -> sfail "Sort_gen_ax"
    , foldExtFORMULA = \ _ f -> mf f
    , foldSimpleId = \ _ _ -> sfail "Simple_id"
    , foldQual_var = \ _ v _ _ -> return $ varToSSymbol v
    , foldApplication = \ _ o rs _ -> do
      ts <- sequence rs
      return $ SList $ SSymbol "fapply" : opToSSymbol o : ts
    , foldSorted_term = \ _ r _ _ -> r
    , foldCast = \ _ _ _ _ -> sfail "Cast"
    , foldConditional = \ _ _ _ _ _ -> sfail "Conditional"
    , foldMixfix_qual_pred = \ _ _ -> sfail "Mixfix_qual_pred"
    , foldMixfix_term = \ _ _ -> sfail "Mixfix_term"
    , foldMixfix_token = \ _ _ -> sfail "Mixfix_token"
    , foldMixfix_sorted_term = \ _ _ _ -> sfail "Mixfix_sorted_term"
    , foldMixfix_cast = \ _ _ _ -> sfail "Mixfix_cast"
    , foldMixfix_parenthesized = \ _ _ _ -> sfail "Mixfix_parenthesized"
    , foldMixfix_bracketed = \ _ _ _ -> sfail "Mixfix_bracketed"
    , foldMixfix_braced = \ _ _ _ -> sfail "Mixfix_braced"
    }
