{- |
Module      :  ./CASL/Fold.hs
Description :  folding functions for CASL terms and formulas
Copyright   :  (c) Christian Maeder, Uni Bremen 2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

folding functions for CASL terms and formulas

-}

module CASL.Fold where

import Common.Id
import CASL.AS_Basic_CASL

data Record f a b = Record
    { foldQuantification :: FORMULA f -> QUANTIFIER -> [VAR_DECL] ->
                          a -> Range -> a
    , foldJunction :: FORMULA f -> Junctor -> [a] -> Range -> a
    , foldRelation :: FORMULA f -> a -> Relation -> a -> Range -> a
    , foldNegation :: FORMULA f -> a -> Range -> a
    , foldAtom :: FORMULA f -> Bool -> Range -> a
    , foldPredication :: FORMULA f -> PRED_SYMB -> [b] -> Range -> a
    , foldDefinedness :: FORMULA f -> b -> Range -> a
    , foldEquation :: FORMULA f -> b -> Equality -> b -> Range -> a
    , foldMembership :: FORMULA f -> b -> SORT -> Range -> a
    , foldMixfix_formula :: FORMULA f -> b -> a
    , foldSort_gen_ax :: FORMULA f -> [Constraint] -> Bool -> a
    , foldQuantOp :: FORMULA f -> OP_NAME -> OP_TYPE -> a -> a
    , foldQuantPred :: FORMULA f -> PRED_NAME -> PRED_TYPE -> a -> a
    , foldExtFORMULA :: FORMULA f -> f -> a
    , foldQual_var :: TERM f -> VAR -> SORT -> Range -> b
    , foldApplication :: TERM f -> OP_SYMB -> [b] -> Range -> b
    , foldSorted_term :: TERM f -> b -> SORT -> Range -> b
    , foldCast :: TERM f -> b -> SORT -> Range -> b
    , foldConditional :: TERM f -> b -> a -> b -> Range -> b
    , foldMixfix_qual_pred :: TERM f -> PRED_SYMB -> b
    , foldMixfix_term :: TERM f -> [b] -> b
    , foldMixfix_token :: TERM f -> Token -> b
    , foldMixfix_sorted_term :: TERM f -> SORT -> Range -> b
    , foldMixfix_cast :: TERM f -> SORT -> Range -> b
    , foldMixfix_parenthesized :: TERM f -> [b] -> Range -> b
    , foldMixfix_bracketed :: TERM f -> [b] -> Range -> b
    , foldMixfix_braced :: TERM f -> [b] -> Range -> b
    , foldExtTERM :: TERM f -> f -> b
    }

mapRecord :: (f -> g) -> Record f (FORMULA g) (TERM g)
mapRecord mf = Record
    { foldQuantification = const Quantification
    , foldJunction = const Junction
    , foldRelation = const Relation
    , foldNegation = const Negation
    , foldAtom = const Atom
    , foldPredication = const Predication
    , foldDefinedness = const Definedness
    , foldEquation = const Equation
    , foldMembership = const Membership
    , foldMixfix_formula = const Mixfix_formula
    , foldSort_gen_ax = const mkSort_gen_ax
    , foldQuantOp = const QuantOp
    , foldQuantPred = const QuantPred
    , foldExtFORMULA = \ _ -> ExtFORMULA . mf
    , foldQual_var = const Qual_var
    , foldApplication = const Application
    , foldSorted_term = const Sorted_term
    , foldCast = const Cast
    , foldConditional = const Conditional
    , foldMixfix_qual_pred = const Mixfix_qual_pred
    , foldMixfix_term = const Mixfix_term
    , foldMixfix_token = const Mixfix_token
    , foldMixfix_sorted_term = const Mixfix_sorted_term
    , foldMixfix_cast = const Mixfix_cast
    , foldMixfix_parenthesized = const Mixfix_parenthesized
    , foldMixfix_bracketed = const Mixfix_bracketed
    , foldMixfix_braced = const Mixfix_braced
    , foldExtTERM = \ _ -> ExtTERM . mf
    }

constRecord :: (f -> a) -> ([a] -> a) -> a -> Record f a a
constRecord mf join c = Record
    { foldQuantification = \ _ _ _ r _ -> r
    , foldJunction = \ _ _ l _ -> join l
    , foldRelation = \ _ l _ r _ -> join [l, r]
    , foldNegation = \ _ r _ -> r
    , foldAtom = \ _ _ _ -> c
    , foldPredication = \ _ _ l _ -> join l
    , foldDefinedness = \ _ r _ -> r
    , foldEquation = \ _ l _ r _ -> join [l, r]
    , foldMembership = \ _ r _ _ -> r
    , foldMixfix_formula = \ _ r -> r
    , foldSort_gen_ax = \ _ _ _ -> c
    , foldQuantOp = \ _ _ _ a -> a
    , foldQuantPred = \ _ _ _ a -> a
    , foldExtFORMULA = const mf
    , foldQual_var = \ _ _ _ _ -> c
    , foldApplication = \ _ _ l _ -> join l
    , foldSorted_term = \ _ r _ _ -> r
    , foldCast = \ _ r _ _ -> r
    , foldConditional = \ _ l f r _ -> join [l, f, r]
    , foldMixfix_qual_pred = \ _ _ -> c
    , foldMixfix_term = const join
    , foldMixfix_token = \ _ _ -> c
    , foldMixfix_sorted_term = \ _ _ _ -> c
    , foldMixfix_cast = \ _ _ _ -> c
    , foldMixfix_parenthesized = \ _ l _ -> join l
    , foldMixfix_bracketed = \ _ l _ -> join l
    , foldMixfix_braced = \ _ l _ -> join l
    , foldExtTERM = const mf
    }

foldFormula :: Record f a b -> FORMULA f -> a
foldFormula r f = case f of
   Quantification q vs e ps -> foldQuantification r f q vs (foldFormula r e) ps
   Junction j fs ps -> foldJunction r f j (map (foldFormula r) fs) ps
   Relation f1 c f2 ps -> foldRelation r f (foldFormula r f1) c
      (foldFormula r f2) ps
   Negation e ps -> foldNegation r f (foldFormula r e) ps
   Atom b ps -> foldAtom r f b ps
   Predication p ts ps -> foldPredication r f p (map (foldTerm r) ts) ps
   Definedness t ps -> foldDefinedness r f (foldTerm r t) ps
   Equation t1 e t2 ps -> foldEquation r f (foldTerm r t1) e
      (foldTerm r t2) ps
   Membership t s ps -> foldMembership r f (foldTerm r t) s ps
   Mixfix_formula t -> foldMixfix_formula r f (foldTerm r t)
   Unparsed_formula s _ -> error $ "Fold.foldFormula.Unparsed" ++ s
   Sort_gen_ax cs b -> foldSort_gen_ax r f cs b
   QuantOp o t q -> foldQuantOp r f o t $ foldFormula r q
   QuantPred p t q -> foldQuantPred r f p t $ foldFormula r q
   ExtFORMULA e -> foldExtFORMULA r f e

foldTerm :: Record f a b -> TERM f -> b
foldTerm r = foldOnlyTerm (foldFormula r) r

foldOnlyTerm :: (FORMULA f -> a) -> Record f a b -> TERM f -> b
foldOnlyTerm ff r t = case t of
   Qual_var v s ps -> foldQual_var r t v s ps
   Application o ts ps -> foldApplication r t o (map (foldOnlyTerm ff r) ts) ps
   Sorted_term st s ps -> foldSorted_term r t (foldOnlyTerm ff r st) s ps
   Cast ct s ps -> foldCast r t (foldOnlyTerm ff r ct) s ps
   Conditional t1 f t2 ps -> foldConditional r t (foldOnlyTerm ff r t1)
      (ff f) (foldOnlyTerm ff r t2) ps
   Unparsed_term s _ -> error $ "Fold.Unparsed_term" ++ s
   Mixfix_qual_pred p -> foldMixfix_qual_pred r t p
   Mixfix_term ts -> foldMixfix_term r t (map (foldOnlyTerm ff r) ts)
   Mixfix_token s -> foldMixfix_token r t s
   Mixfix_sorted_term s ps -> foldMixfix_sorted_term r t s ps
   Mixfix_cast s ps -> foldMixfix_cast r t s ps
   Mixfix_parenthesized ts ps -> foldMixfix_parenthesized r t
      (map (foldOnlyTerm ff r) ts) ps
   Mixfix_bracketed ts ps -> foldMixfix_bracketed r t
      (map (foldOnlyTerm ff r) ts) ps
   Mixfix_braced ts ps -> foldMixfix_braced r t
      (map (foldOnlyTerm ff r) ts) ps
   ExtTERM e -> foldExtTERM r t e
