{- |
Module      :  ./CASL/CompositionTable/ModelFormula.hs
Description :  intermediate calculus formula
Copyright   :  (c) DFKI Bremen 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module CASL.CompositionTable.ModelFormula where

import CASL.AS_Basic_CASL
import CASL.Fold

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.List

data Form
  = Quant QUANTIFIER [Int] Form
  | Junct Bool [Form]  -- True for and, False for or
  | Impl Bool Form Form  -- True for => False for <=>
  | Neg Form
  | Const Bool
  | Eq Term Term

data Term
  = Cond Term Form Term
  | Appl Op [Term]
  | Var Int

data Op =
    Comp | Inter | Union
  | Compl | Conv | Shortcut | Inv | Home
  | One | Iden | Zero

getVars :: [VAR_DECL] -> [VAR]
getVars = concatMap (\ (Var_decl vs _ _) -> vs)

vars :: FORMULA f -> Set.Set VAR
vars = foldFormula (constRecord (const Set.empty) Set.unions Set.empty)
    { foldQual_var = \ _ v _ _ -> Set.singleton v
    , foldQuantification = \ _ _ vdecl phiVars _ ->
           Set.union phiVars $ Set.fromList $ getVars vdecl
    }

lkup :: Map.Map VAR Int -> VAR -> Int
lkup = flip $ Map.findWithDefault (error "CompositionTable.lkup")

getOp :: String -> Op
getOp s = let err = error "CompositionTable.getOp" in
  case stripPrefix "RA_" s of
  Just r -> case r of
    "composition" -> Comp
    "intersection" -> Inter
    "union" -> Union
    "complement" -> Compl
    "converse" -> Conv
    "shortcut" -> Shortcut
    "inverse" -> Inv
    "homing" -> Home
    "one" -> One
    "identity" -> Iden
    "zero" -> Zero
    _ -> err
  Nothing -> err

fromCASL :: Map.Map OP_SYMB String -> Map.Map VAR Int -> Record f Form Term
fromCASL oM m = let err = error "CompositionTable.CASLFormula" in Record
    { foldQuantification = \ _ q vs f _ ->
        Quant q (map (lkup m) $ getVars vs) f
    , foldJunction = \ _ k as _ -> Junct (k == Con) as
    , foldRelation = \ _ f r g _ -> Impl (r /= Equivalence) f g
    , foldNegation = \ _ f _ -> Neg f
    , foldAtom = \ _ b _ -> Const b
    , foldPredication = err
    , foldDefinedness = err
    , foldEquation = \ _ t _ s _ -> Eq t s
    , foldMembership = err
    , foldMixfix_formula = err
    , foldSort_gen_ax = err
    , foldQuantOp = err
    , foldQuantPred = err
    , foldExtFORMULA = err
    , foldQual_var = \ _ v _ _ -> Var $ lkup m v
    , foldApplication = \ _ op ts _ ->
        Appl (getOp $ Map.findWithDefault "" op oM) ts
    , foldSorted_term = \ _ t _ _ -> t
    , foldCast = \ _ t _ _ -> t
    , foldConditional = \ _ t f s _ -> Cond t f s
    , foldMixfix_qual_pred = err
    , foldMixfix_term = err
    , foldMixfix_token = err
    , foldMixfix_sorted_term = err
    , foldMixfix_cast = err
    , foldMixfix_parenthesized = err
    , foldMixfix_bracketed = err
    , foldMixfix_braced = err
    , foldExtTERM = err
    }
